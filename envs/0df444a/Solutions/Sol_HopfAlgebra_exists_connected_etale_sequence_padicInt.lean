-- Prove2me | solution 1 for HopfAlgebra.exists_connected_etale_sequence_padicInt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/d9bb83aa-530a-54be-aaf4-cb2c47cc89b8

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_HopfAlgebra_HopfKer
import Definitions.Def_HopfAlgebra_HopfKerHopf
import Theorems.Thm_HopfAlgebra_exists_hopfAlgebra_bialgHom_surjective_ker_eq_of_hopfIdeal_of_commRing
import Theorems.Thm_HopfAlgebra_finite_free_hopfKer_of_isPrincipalIdealRing
import Theorems.Thm_HopfAlgebra_isHopfGalois_of_surjective
import Theorems.Thm_HopfAlgebra_finrank_hopfKer_mul_finrank_of_surjective
import Theorems.Thm_HopfAlgebra_algHom_comp_hopfKer_val_eq_iff
import Theorems.Thm_HopfAlgebra_natCard_algHom_eq_finrank_of_charZero
import Theorems.Thm_HopfAlgebra_formallyUnramified_of_ker_counit_eq_sq
import Theorems.Thm_IsAdicComplete_exists_isIdempotentElem_apply_eq_zero_isLocalRing_quotient
import Theorems.Thm_Algebra_TensorProduct_ker_lift_le_jacobson_of_isLocalRing
import Theorems.Thm_Algebra_FormallyUnramified_algEquiv_apply_eq_of_mem_inertiaSubgroupIn_padicIntegers
import Theorems.Thm_Subalgebra_exists_algHom_comp_val_eq_of_isAlgClosed_of_moduleFinite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_connected_etale_sequence_padicInt

set_option autoImplicit false

open scoped PadicInt TensorProduct

universe u v w

namespace S3Assembly

section Glue

variable {R : Type u} [CommRing R]

theorem glue_lift_id_counit_comul {A : Type v} [CommRing A] [Bialgebra R A] (a : A) :
    Algebra.TensorProduct.lift (AlgHom.id R A) ((Algebra.ofId R A).comp (Bialgebra.counitAlgHom R A))
      (fun _ _ => Commute.all _ _) (Coalgebra.comul (R := R) a) = a := by
  classical
  let 𝓡 := Coalgebra.Repr.arbitrary R a
  conv_lhs => rw [← 𝓡.eq]
  rw [map_sum]
  simp only [Algebra.TensorProduct.lift_tmul, AlgHom.coe_id, id_eq, AlgHom.coe_comp, Function.comp_apply]
  have h3 : ∀ i ∈ 𝓡.index,
      𝓡.left i * (Algebra.ofId R A) (Bialgebra.counitAlgHom R A (𝓡.right i))
        = Coalgebra.counit (R := R) (𝓡.right i) • 𝓡.left i := by
    intro i _
    rw [mul_comm, Algebra.smul_def]
    rfl
  rw [Finset.sum_congr rfl h3]
  have := congr(TensorProduct.rid R A $(Coalgebra.sum_tmul_counit_eq (R := R) 𝓡))
  simp only [map_sum, TensorProduct.rid_tmul, one_smul] at this
  exact this

theorem glue_eq_of_isIdempotentElem_of_lift_eq [IsLocalRing R]
    {C : Type v} [CommRing C] [Algebra R C] [Module.Finite R C]
    {D : Type w} [CommRing D] [Algebra R D] [Module.Finite R D] [IsLocalRing D]
    (ε : D →ₐ[R] R) {x y : C ⊗[R] D} (hx : IsIdempotentElem x) (hy : IsIdempotentElem y)
    (h : Algebra.TensorProduct.lift (AlgHom.id R C) ((Algebra.ofId R C).comp ε)
        (fun _ _ => Commute.all _ _) x =
      Algebra.TensorProduct.lift (AlgHom.id R C) ((Algebra.ofId R C).comp ε)
        (fun _ _ => Commute.all _ _) y) :
    x = y := by
  set z := x - y with hz
  have hzJ : z ∈ Ideal.jacobson (⊥ : Ideal (C ⊗[R] D)) := by
    apply Algebra.TensorProduct.ker_lift_le_jacobson_of_isLocalRing ε
    rw [RingHom.mem_ker, map_sub, sub_eq_zero]
    exact h
  have hz3 : z * (1 - z ^ 2) = 0 := by
    have hx' : x * x = x := hx.eq
    have hy' : y * y = y := hy.eq
    simp only [hz]
    linear_combination (-(x + 1 - 3 * y)) * hx' + (-(3 * x - (y + 1))) * hy'
  have hu : IsUnit (1 - z ^ 2) := by
    have := Ideal.mem_jacobson_bot.mp hzJ (-z)
    convert this using 1
    ring
  have : z = 0 := by
    obtain ⟨u, hu⟩ := hu
    have := congrArg (· * (↑u⁻¹ : C ⊗[R] D)) hz3
    simp only [zero_mul] at this
    rw [← hu, mul_assoc, Units.mul_inv, mul_one] at this
    exact this
  exact sub_eq_zero.mp this

variable {H : Type v} [CommRing H] [HopfAlgebra R H]

theorem glue_apply_eq_algebraMap_counit_of_mem_hopfKer {B : Type w} [CommRing B] [Bialgebra R B]
    (π : H →ₐc[R] B) {a : H} (ha : a ∈ HopfAlgebra.hopfKer π) :
    π a = algebraMap R B (Coalgebra.counit (R := R) a) := by
  classical
  let 𝓡 := Coalgebra.Repr.arbitrary R a
  let Φ : H ⊗[R] B →ₐ[R] B :=
    Algebra.TensorProduct.lift ((Algebra.ofId R B).comp (Bialgebra.counitAlgHom R H)) (AlgHom.id R B)
      (fun _ _ => Commute.all _ _)
  have h1 : HopfAlgebra.coaction π a = a ⊗ₜ[R] 1 := ha
  have h2 := congrArg Φ h1
  rw [HopfAlgebra.coaction_apply, ← 𝓡.eq, map_sum, map_sum] at h2
  simp only [Φ, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul, AlgHom.coe_comp,
    Function.comp_apply, AlgHom.coe_id, id_eq, map_one, mul_one] at h2
  change π a = (Algebra.ofId R B) ((Bialgebra.counitAlgHom R H) a)
  rw [← h2]
  have h3 : ∀ i ∈ 𝓡.index,
      (Algebra.ofId R B) (Bialgebra.counitAlgHom R H (𝓡.left i)) * (π : H →ₐ[R] B) (𝓡.right i)
        = π (Coalgebra.counit (R := R) (𝓡.left i) • 𝓡.right i) := by
    intro i _
    rw [map_smul, Algebra.smul_def]
    rfl
  rw [Finset.sum_congr rfl h3, ← map_sum, Coalgebra.sum_counit_smul 𝓡]

theorem glue_counit_mem_span (e : H) (hεe : Coalgebra.counit (R := R) e = 0) :
    ∀ a ∈ Ideal.span ({e} : Set H), Coalgebra.counit (R := R) a = 0 := by
  intro a ha
  obtain ⟨x, rfl⟩ := Ideal.mem_span_singleton'.mp ha
  have : Coalgebra.counit (R := R) (x * e)
      = Bialgebra.counitAlgHom R H x * Bialgebra.counitAlgHom R H e := by
    rw [← map_mul]; rfl
  rw [this]
  change _ * Coalgebra.counit (R := R) e = 0
  rw [hεe, mul_zero]

noncomputable def counitQuot (e : H) (hεe : Coalgebra.counit (R := R) e = 0) :
    (H ⧸ Ideal.span ({e} : Set H)) →ₐ[R] R :=
  Ideal.Quotient.liftₐ (Ideal.span ({e} : Set H)) (Bialgebra.counitAlgHom R H)
    (fun a ha => glue_counit_mem_span e hεe a ha)

theorem counitQuot_mk (e : H) (hεe : Coalgebra.counit (R := R) e = 0) (a : H) :
    counitQuot e hεe (Ideal.Quotient.mk _ a) = Coalgebra.counit (R := R) a := rfl

theorem isIdempotentElem_eq_zero_or_one_of_isLocalRing {S : Type*} [CommRing S] [IsLocalRing S] {x : S}
    (hx : IsIdempotentElem x) : x = 0 ∨ x = 1 := by
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self x with h | h
  · right
    obtain ⟨u, rfl⟩ := h
    have hu : (u : S) * u = u := hx.eq
    calc (u : S) = ↑u⁻¹ * (↑u * ↑u) := by rw [← mul_assoc, Units.inv_mul, one_mul]
      _ = ↑u⁻¹ * ↑u := by rw [hu]
      _ = 1 := Units.inv_mul u
  · left
    obtain ⟨u, hu⟩ := h
    have h0 : x * (1 - x) = 0 := hx.mul_one_sub_self
    rw [← hu] at h0
    have := congrArg (· * (↑u⁻¹ : S)) h0
    simpa using this

theorem isIdempotentElem_eq_zero_of_map_eq_zero {S T : Type*} [CommRing S] [IsLocalRing S] [CommRing T]
    [Nontrivial T] (f : S →+* T) {x : S} (hx : IsIdempotentElem x) (hfx : f x = 0) : x = 0 := by
  rcases isIdempotentElem_eq_zero_or_one_of_isLocalRing hx with h | h
  · exact h
  · rw [h, map_one] at hfx
    exact absurd hfx one_ne_zero

theorem glue_antipode_mem_span [Nontrivial R] (e : H) (he : IsIdempotentElem e)
    (hεe : Coalgebra.counit (R := R) e = 0) (hloc : IsLocalRing (H ⧸ Ideal.span ({e} : Set H))) :
    ∀ a ∈ Ideal.span ({e} : Set H), HopfAlgebraStruct.antipode (R := R) a ∈ Ideal.span ({e} : Set H) := by
  intro a ha
  obtain ⟨x, rfl⟩ := Ideal.mem_span_singleton'.mp ha
  rw [HopfAlgebra.antipode_mul]
  apply Ideal.mul_mem_right
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  haveI := hloc
  apply isIdempotentElem_eq_zero_of_map_eq_zero (counitQuot e hεe).toRingHom
  · change Ideal.Quotient.mk _ _ * Ideal.Quotient.mk _ _ = _
    rw [← map_mul, ← HopfAlgebra.antipode_mul, he.eq]
  · change counitQuot e hεe (Ideal.Quotient.mk _ (HopfAlgebraStruct.antipode (R := R) e)) = 0
    rw [counitQuot_mk, HopfAlgebra.counit_antipode, hεe]

theorem glue_comul_mem_span [IsLocalRing R] [Module.Finite R H] (e : H) (he : IsIdempotentElem e)
    (hεe : Coalgebra.counit (R := R) e = 0) (hloc : IsLocalRing (H ⧸ Ideal.span ({e} : Set H))) :
    ∀ a ∈ Ideal.span ({e} : Set H),
      Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R (Ideal.span ({e} : Set H)))
        (Ideal.Quotient.mkₐ R (Ideal.span ({e} : Set H))) (Coalgebra.comul (R := R) a) = 0 := by
  classical
  haveI := hloc
  set I : Ideal H := Ideal.span ({e} : Set H) with hI
  let Ψ : H →ₐ[R] (H ⧸ I) ⊗[R] (H ⧸ I) :=
    (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)).comp
      (Bialgebra.comulAlgHom R H)
  have hΨ : ∀ a, Ψ a = Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)
      (Coalgebra.comul (R := R) a) := fun a => rfl
  have hΨe : Ψ e = 0 := by
    let ε' : (H ⧸ I) →ₐ[R] R := counitQuot e hεe
    let Φ : (H ⧸ I) ⊗[R] (H ⧸ I) →ₐ[R] (H ⧸ I) :=
      Algebra.TensorProduct.lift (AlgHom.id R _) ((Algebra.ofId R _).comp ε') (fun _ _ => Commute.all _ _)
    have hcomp : Φ.comp (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I))
        = (Ideal.Quotient.mkₐ R I).comp (Algebra.TensorProduct.lift (AlgHom.id R H)
            ((Algebra.ofId R H).comp (Bialgebra.counitAlgHom R H)) (fun _ _ => Commute.all _ _)) := by
      apply Algebra.TensorProduct.ext'
      intro a b
      simp only [Φ, ε', AlgHom.coe_comp, Function.comp_apply, Algebra.TensorProduct.map_tmul,
        Algebra.TensorProduct.lift_tmul, AlgHom.coe_id, id_eq, Ideal.Quotient.mkₐ_eq_mk, map_mul]
      congr 1
    have h1 : Φ (Ψ e) = 0 := by
      change (Φ.comp (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)))
        (Coalgebra.comul (R := R) e) = 0
      rw [hcomp, AlgHom.comp_apply, glue_lift_id_counit_comul, Ideal.Quotient.mkₐ_eq_mk,
        Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span rfl
    have hidem : IsIdempotentElem (Ψ e) := he.map Ψ
    exact glue_eq_of_isIdempotentElem_of_lift_eq ε' hidem IsIdempotentElem.zero (by rw [h1, map_zero])
  intro a ha
  obtain ⟨x, rfl⟩ := Ideal.mem_span_singleton'.mp ha
  rw [← hΨ, map_mul, hΨe, mul_zero]

theorem glue_mem_hopfKer [IsLocalRing R] [Module.Finite R H] {B : Type w} [CommRing B] [Bialgebra R B]
    [Module.Finite R B] [IsLocalRing B] (π : H →ₐc[R] B) {e : H} (he : IsIdempotentElem e) :
    e ∈ HopfAlgebra.hopfKer π := by
  classical
  rw [HopfAlgebra.mem_hopfKer_iff]
  let ε₀ : B →ₐ[R] R := Bialgebra.counitAlgHom R B
  let Φ : H ⊗[R] B →ₐ[R] H :=
    Algebra.TensorProduct.lift (AlgHom.id R H) ((Algebra.ofId R H).comp ε₀) (fun _ _ => Commute.all _ _)
  have hcomp : Φ.comp (Algebra.TensorProduct.map (AlgHom.id R H) (π : H →ₐ[R] B))
      = Algebra.TensorProduct.lift (AlgHom.id R H) ((Algebra.ofId R H).comp (Bialgebra.counitAlgHom R H))
          (fun _ _ => Commute.all _ _) := by
    apply Algebra.TensorProduct.ext'
    intro a b
    simp only [Φ, ε₀, AlgHom.coe_comp, Function.comp_apply, Algebra.TensorProduct.map_tmul,
      Algebra.TensorProduct.lift_tmul, AlgHom.coe_id, id_eq]
    congr 2
    change Coalgebra.counit (R := R) (π b) = Coalgebra.counit (R := R) b
    exact CoalgHomClass.counit_comp_apply π b
  have hx : IsIdempotentElem (HopfAlgebra.coaction π e) := he.map _
  have hy : IsIdempotentElem (e ⊗ₜ[R] (1 : B)) := by
    change (e ⊗ₜ[R] (1 : B)) * (e ⊗ₜ[R] (1 : B)) = e ⊗ₜ[R] (1 : B)
    rw [Algebra.TensorProduct.tmul_mul_tmul, he.eq, mul_one]
  refine glue_eq_of_isIdempotentElem_of_lift_eq ε₀ hx hy ?_
  change (Φ.comp (Algebra.TensorProduct.map (AlgHom.id R H) (π : H →ₐ[R] B))) (Coalgebra.comul (R := R) e)
    = Φ (e ⊗ₜ[R] (1 : B))
  rw [hcomp, glue_lift_id_counit_comul]
  simp [Φ, Algebra.TensorProduct.lift_tmul]

theorem glue_isLocalRing_of_surjective {B : Type w} [CommRing B] (f : H →+* B) (hf : Function.Surjective f)
    (I : Ideal H) (hI : RingHom.ker f = I) (hloc : IsLocalRing (H ⧸ I)) : IsLocalRing B := by
  subst hI
  have e := RingHom.quotientKerEquivOfSurjective hf
  haveI : Nontrivial B := e.symm.toEquiv.nontrivial
  exact IsLocalRing.of_surjective' e.toRingHom e.surjective

theorem glue_free_of_surjective_ker_eq_span [IsDomain R] [IsPrincipalIdealRing R] [Module.Finite R H]
    [Module.Free R H] {B : Type w} [CommRing B] [Algebra R B] (f : H →ₐ[R] B)
    (hf : Function.Surjective f) {e : H} (he : IsIdempotentElem e)
    (hI : RingHom.ker (f : H →+* B) = Ideal.span ({e} : Set H)) : Module.Free R B := by
  haveI : Module.Finite R B := Module.Finite.of_surjective f.toLinearMap hf
  haveI : NoZeroSMulDivisors R B := by
    refine ⟨fun {r x} hrx => ?_⟩
    obtain ⟨h, rfl⟩ := hf x
    by_cases hr : r = 0
    · exact Or.inl hr
    right
    rw [← map_smul] at hrx
    have hmem : r • h ∈ RingHom.ker (f : H →+* B) := hrx
    rw [hI] at hmem
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hmem

    have h0 : r • (h - h * e) = 0 := by
      rw [smul_sub, ← smul_mul_assoc, ← hy, mul_assoc, he.eq, sub_self]
    have h1 : h - h * e = 0 := by
      rcases smul_eq_zero.mp h0 with h0 | h0
      · exact absurd h0 hr
      · exact h0
    have h2 : h = h * e := sub_eq_zero.mp h1
    have he0 : f e = 0 := by
      have : e ∈ RingHom.ker (f : H →+* B) := by rw [hI]; exact Ideal.subset_span rfl
      exact this
    rw [h2, map_mul, he0, mul_zero]
  exact Module.free_of_finite_type_torsion_free'

section Ker

variable {B : Type w} [CommRing B] [HopfAlgebra R B] (π : H →ₐc[R] B)
variable [Coalgebra.IsCocomm R H] [Module.Flat R H] [Module.Flat R B] [Module.Flat R ↥(HopfAlgebra.hopfKer π)]

theorem glue_ker_counit_hopfKer_eq_span {e : H} (he : IsIdempotentElem e)
    (he_mem : e ∈ HopfAlgebra.hopfKer π) (hεe : Coalgebra.counit (R := R) e = 0)
    (hker : RingHom.ker (π : H →+* B) = Ideal.span ({e} : Set H)) :
    RingHom.ker (Bialgebra.counitAlgHom R ↥(HopfAlgebra.hopfKer π))
      = Ideal.span ({(⟨e, he_mem⟩ : ↥(HopfAlgebra.hopfKer π))} : Set ↥(HopfAlgebra.hopfKer π)) := by
  apply le_antisymm
  · intro a ha
    have ha0 : Coalgebra.counit (R := R) (a : H) = 0 := ha
    have hπa : π (a : H) = 0 := by
      rw [glue_apply_eq_algebraMap_counit_of_mem_hopfKer π a.2, ha0, map_zero]
    have hmem : (a : H) ∈ RingHom.ker (π : H →+* B) := hπa
    rw [hker] at hmem
    obtain ⟨x, hx⟩ := Ideal.mem_span_singleton'.mp hmem
    have hae : (a : H) * e = a := by rw [← hx, mul_assoc, he.eq]
    refine Ideal.mem_span_singleton'.mpr ⟨a, Subtype.ext ?_⟩
    exact hae
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hεe

theorem glue_comp_hopfKerVal_eq_iff (hHG : HopfAlgebra.IsHopfGalois π) (hπ : Function.Surjective π)
    {K : Type*} [CommRing K] [Algebra R K] (f : H →ₐ[R] K) :
    f.comp (HopfAlgebra.hopfKerVal π : ↥(HopfAlgebra.hopfKer π) →ₐ[R] H) =
        (Algebra.ofId R K).comp (Bialgebra.counitAlgHom R ↥(HopfAlgebra.hopfKer π)) ↔
      ∃ g : B →ₐ[R] K, f = g.comp (π : H →ₐ[R] B) := by
  classical
  have hval : (HopfAlgebra.hopfKerVal π : ↥(HopfAlgebra.hopfKer π) →ₐ[R] H)
      = (HopfAlgebra.hopfKer π).val := AlgHom.ext fun _ => rfl
  have hcounit : (Algebra.ofId R K).comp (Bialgebra.counitAlgHom R ↥(HopfAlgebra.hopfKer π))
      = ((Algebra.ofId R K).comp (Bialgebra.counitAlgHom R H)).comp (HopfAlgebra.hopfKer π).val :=
    AlgHom.ext fun _ => rfl

  have key := HopfAlgebra.algHom_comp_hopfKer_val_eq_iff π hHG
    ((Algebra.ofId R K).comp (Bialgebra.counitAlgHom R H)) f

  have hlift : ∀ χ : B →ₐ[R] K,
      (Algebra.TensorProduct.lift ((Algebra.ofId R K).comp (Bialgebra.counitAlgHom R H)) χ
          (fun _ _ => Commute.all _ _)).comp (HopfAlgebra.coaction π) = χ.comp (π : H →ₐ[R] B) := by
    intro χ
    apply AlgHom.ext
    intro a
    let 𝓡 := Coalgebra.Repr.arbitrary R a
    rw [AlgHom.comp_apply, HopfAlgebra.coaction_apply, ← 𝓡.eq, map_sum, map_sum]
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, Algebra.TensorProduct.lift_tmul,
      AlgHom.coe_comp, Function.comp_apply]
    have h3 : ∀ i ∈ 𝓡.index,
        (Algebra.ofId R K) (Bialgebra.counitAlgHom R H (𝓡.left i)) * χ ((π : H →ₐ[R] B) (𝓡.right i))
          = (χ.comp (π : H →ₐ[R] B)) (Coalgebra.counit (R := R) (𝓡.left i) • 𝓡.right i) := by
      intro i _
      rw [map_smul, Algebra.smul_def]
      rfl
    rw [Finset.sum_congr rfl h3, ← map_sum, Coalgebra.sum_counit_smul 𝓡]
    rfl
  rw [hval, hcounit, eq_comm, key]
  constructor
  · rintro ⟨χ, hχ, -⟩
    rw [hlift] at hχ
    exact ⟨χ, hχ.symm⟩
  · rintro ⟨g, rfl⟩
    refine ⟨g, ?_, fun χ hχ => ?_⟩
    · beta_reduce
      rw [hlift]
    · beta_reduce at hχ
      rw [hlift] at hχ
      apply AlgHom.ext
      intro b
      obtain ⟨a, rfl⟩ := hπ b
      exact congrArg (fun φ : H →ₐ[R] K => φ a) hχ

end Ker

end Glue

set_option maxHeartbeats 1600000 in
theorem s3_main
    (p : ℕ) [Fact p.Prime]
    (H : Type) [CommRing H] [HopfAlgebra ℤ_[p] H] [Module.Finite ℤ_[p] H] [Module.Free ℤ_[p] H]
    [Coalgebra.IsCocomm ℤ_[p] H] :
    ∃ (H₀ : Type) (_ : CommRing H₀) (_ : HopfAlgebra ℤ_[p] H₀) (Hₑ : Type) (_ : CommRing Hₑ)
      (_ : HopfAlgebra ℤ_[p] Hₑ) (π : H →ₐc[ℤ_[p]] H₀) (ι : Hₑ →ₐc[ℤ_[p]] H),
      Module.Finite ℤ_[p] H₀ ∧ Module.Free ℤ_[p] H₀ ∧ Coalgebra.IsCocomm ℤ_[p] H₀ ∧ IsLocalRing H₀ ∧
      Module.Finite ℤ_[p] Hₑ ∧ Module.Free ℤ_[p] Hₑ ∧ Coalgebra.IsCocomm ℤ_[p] Hₑ ∧
        Algebra.Etale ℤ_[p] Hₑ ∧
      Function.Surjective π ∧ (∃ e : H, IsIdempotentElem e ∧ RingHom.ker π = Ideal.span {e}) ∧
      Function.Injective ι ∧ (∀ x : H, x ∈ HopfAlgebra.hopfKer π ↔ x ∈ Set.range ι) ∧
      Module.finrank ℤ_[p] H = Module.finrank ℤ_[p] H₀ * Module.finrank ℤ_[p] Hₑ ∧
      Nat.card (Hₑ →ₐ[ℤ_[p]] PadicAlgCl p) = Module.finrank ℤ_[p] Hₑ ∧
      (∀ f : H →ₐ[ℤ_[p]] PadicAlgCl p,
        f.comp (ι : Hₑ →ₐ[ℤ_[p]] H) =
            (Algebra.ofId ℤ_[p] (PadicAlgCl p)).comp (Bialgebra.counitAlgHom ℤ_[p] Hₑ) ↔
          ∃ g : H₀ →ₐ[ℤ_[p]] PadicAlgCl p, f = g.comp (π : H →ₐ[ℤ_[p]] H₀)) ∧
      (∀ h : Hₑ →ₐ[ℤ_[p]] PadicAlgCl p, ∃ f : H →ₐ[ℤ_[p]] PadicAlgCl p,
        f.comp (ι : Hₑ →ₐ[ℤ_[p]] H) = h) ∧
      (∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] →
        ∀ (h : Hₑ →ₐ[ℤ_[p]] PadicAlgCl p) (y : Hₑ), σ (h y) = h y) := by
  classical

  obtain ⟨e, he, hεe, hloc⟩ :=
    IsAdicComplete.exists_isIdempotentElem_apply_eq_zero_isLocalRing_quotient
      (R := ℤ_[p]) (S := H) (Bialgebra.counitAlgHom ℤ_[p] H)
  have hεe' : Coalgebra.counit (R := ℤ_[p]) e = 0 := hεe

  obtain ⟨H₀, instCR, instHA, π, hπsurj, hker, hcocomm, hfin, huniv⟩ :=
    HopfAlgebra.exists_hopfAlgebra_bialgHom_surjective_ker_eq_of_hopfIdeal_of_commRing
      (R := ℤ_[p]) (A := H) (Ideal.span ({e} : Set H))
      (glue_comul_mem_span (R := ℤ_[p]) e he hεe' hloc)
      (glue_counit_mem_span (R := ℤ_[p]) e hεe')
      (glue_antipode_mem_span (R := ℤ_[p]) e he hεe' hloc)
  haveI : Module.Finite ℤ_[p] H₀ := hfin inferInstance
  haveI hcocomm₀ : Coalgebra.IsCocomm ℤ_[p] H₀ := hcocomm inferInstance

  haveI hloc₀ : IsLocalRing H₀ :=
    glue_isLocalRing_of_surjective (π : H →+* H₀) hπsurj _ hker hloc

  haveI hfree₀ : Module.Free ℤ_[p] H₀ :=
    glue_free_of_surjective_ker_eq_span (π : H →ₐ[ℤ_[p]] H₀) hπsurj he hker
  haveI : Module.Flat ℤ_[p] H₀ := inferInstance

  obtain ⟨hfinₑ, hfreeₑ⟩ :=
    HopfAlgebra.finite_free_hopfKer_of_isPrincipalIdealRing (R := ℤ_[p]) (A := H) (B := H₀) π
  haveI := hfinₑ
  haveI := hfreeₑ
  haveI : Module.Flat ℤ_[p] ↥(HopfAlgebra.hopfKer π) := inferInstance
  haveI : Module.Flat ℤ_[p] H := inferInstance

  have he_mem : e ∈ HopfAlgebra.hopfKer π := glue_mem_hopfKer π he
  have hkerε : RingHom.ker (Bialgebra.counitAlgHom ℤ_[p] ↥(HopfAlgebra.hopfKer π))
      = Ideal.span ({(⟨e, he_mem⟩ : ↥(HopfAlgebra.hopfKer π))} : Set ↥(HopfAlgebra.hopfKer π)) :=
    glue_ker_counit_hopfKer_eq_span π he he_mem hεe' hker
  have hkerε2 : RingHom.ker (Bialgebra.counitAlgHom ℤ_[p] ↥(HopfAlgebra.hopfKer π))
      = RingHom.ker (Bialgebra.counitAlgHom ℤ_[p] ↥(HopfAlgebra.hopfKer π)) ^ 2 := by
    rw [hkerε, Ideal.span_singleton_pow]
    congr 2
    exact Subtype.ext (by simpa [pow_two] using he.eq.symm)
  haveI hunr : Algebra.FormallyUnramified ℤ_[p] ↥(HopfAlgebra.hopfKer π) :=
    HopfAlgebra.formallyUnramified_of_ker_counit_eq_sq hkerε2
  haveI : Algebra.FinitePresentation ℤ_[p] ↥(HopfAlgebra.hopfKer π) :=
    (Algebra.FinitePresentation.of_finiteType (R := ℤ_[p])).mp inferInstance
  have hetale : Algebra.Etale ℤ_[p] ↥(HopfAlgebra.hopfKer π) := Algebra.Etale.of_formallyUnramified_of_flat

  have hHG : HopfAlgebra.IsHopfGalois π := HopfAlgebra.isHopfGalois_of_surjective π hπsurj

  refine ⟨H₀, instCR, instHA, ↥(HopfAlgebra.hopfKer π), inferInstance, inferInstance, π,
    HopfAlgebra.hopfKerVal π, inferInstance, hfree₀, hcocomm₀, hloc₀, hfinₑ, hfreeₑ, inferInstance, hetale,
    hπsurj, ⟨e, he, ?_⟩, HopfAlgebra.hopfKerVal_injective π, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    exact hker
  ·
    intro x
    constructor
    · intro hx; exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨s, rfl⟩; exact s.2
  ·
    have := HopfAlgebra.finrank_hopfKer_mul_finrank_of_surjective (R := ℤ_[p]) π hπsurj
    rw [← this, mul_comm]
  ·
    exact HopfAlgebra.natCard_algHom_eq_finrank_of_charZero ℤ_[p] ↥(HopfAlgebra.hopfKer π) (PadicAlgCl p)
  ·
    intro f
    exact glue_comp_hopfKerVal_eq_iff π hHG hπsurj f
  ·
    intro h
    obtain ⟨ν, hν⟩ := Subalgebra.exists_algHom_comp_val_eq_of_isAlgClosed_of_moduleFinite
      (R := ℤ_[p]) (A := H) (HopfAlgebra.hopfKer π) (PadicAlgCl p) h
    exact ⟨ν, by rw [← hν]; rfl⟩
  ·
    intro σ hσ h y
    exact Algebra.FormallyUnramified.algEquiv_apply_eq_of_mem_inertiaSubgroupIn_padicIntegers p
      ↥(HopfAlgebra.hopfKer π) σ hσ h y

end S3Assembly

theorem solution
    (p : ℕ) [Fact p.Prime]
    (H : Type) [CommRing H] [HopfAlgebra ℤ_[p] H] [Module.Finite ℤ_[p] H] [Module.Free ℤ_[p] H]
    [Coalgebra.IsCocomm ℤ_[p] H] :
    ∃ (H₀ : Type) (_ : CommRing H₀) (_ : HopfAlgebra ℤ_[p] H₀) (Hₑ : Type) (_ : CommRing Hₑ)
      (_ : HopfAlgebra ℤ_[p] Hₑ) (π : H →ₐc[ℤ_[p]] H₀) (ι : Hₑ →ₐc[ℤ_[p]] H),
      Module.Finite ℤ_[p] H₀ ∧ Module.Free ℤ_[p] H₀ ∧ Coalgebra.IsCocomm ℤ_[p] H₀ ∧ IsLocalRing H₀ ∧
      Module.Finite ℤ_[p] Hₑ ∧ Module.Free ℤ_[p] Hₑ ∧ Coalgebra.IsCocomm ℤ_[p] Hₑ ∧
        Algebra.Etale ℤ_[p] Hₑ ∧
      Function.Surjective π ∧ (∃ e : H, IsIdempotentElem e ∧ RingHom.ker π = Ideal.span {e}) ∧
      Function.Injective ι ∧ (∀ x : H, x ∈ HopfAlgebra.hopfKer π ↔ x ∈ Set.range ι) ∧
      Module.finrank ℤ_[p] H = Module.finrank ℤ_[p] H₀ * Module.finrank ℤ_[p] Hₑ ∧
      Nat.card (Hₑ →ₐ[ℤ_[p]] PadicAlgCl p) = Module.finrank ℤ_[p] Hₑ ∧
      (∀ f : H →ₐ[ℤ_[p]] PadicAlgCl p,
        f.comp (ι : Hₑ →ₐ[ℤ_[p]] H) =
            (Algebra.ofId ℤ_[p] (PadicAlgCl p)).comp (Bialgebra.counitAlgHom ℤ_[p] Hₑ) ↔
          ∃ g : H₀ →ₐ[ℤ_[p]] PadicAlgCl p, f = g.comp (π : H →ₐ[ℤ_[p]] H₀)) ∧
      (∀ h : Hₑ →ₐ[ℤ_[p]] PadicAlgCl p, ∃ f : H →ₐ[ℤ_[p]] PadicAlgCl p,
        f.comp (ι : Hₑ →ₐ[ℤ_[p]] H) = h) ∧
      (∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] →
        ∀ (h : Hₑ →ₐ[ℤ_[p]] PadicAlgCl p) (y : Hₑ), σ (h y) = h y) :=
  S3Assembly.s3_main p H

end S_HopfAlgebra_exists_connected_etale_sequence_padicInt
end P2MW
export P2MW.S_HopfAlgebra_exists_connected_etale_sequence_padicInt (solution)
