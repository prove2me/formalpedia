-- Prove2me | solution 1 for HopfAlgebra.exists_bialgHom_surjective_isLocalRing_tensorProduct_forall_point_comp_eq_of_henselianLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/889d1fdb-af83-57ff-ace7-3514a6c5f4bd

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_HopfAlgebra_HopfIdealQuotient
import Theorems.Thm_HenselianLocalRing_exists_completeOrthogonalIdempotents_forall_isLocalRing_quotient_of_moduleFinite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_bialgHom_surjective_isLocalRing_tensorProduct_forall_point_comp_eq_of_henselianLocalRing

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped TensorProduct

namespace ConnComp

section Idem

variable {L : Type*} [CommRing L]

theorem idem_eq_zero_of_mem [IsLocalRing L] {x : L} (hx : IsIdempotentElem x)
    (hm : x ∈ IsLocalRing.maximalIdeal L) : x = 0 := by
  have hu : IsUnit (1 - x) := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits x hm
  have h0 : x * (1 - x) = 0 := by rw [mul_sub, mul_one, hx.eq, sub_self]
  exact (IsUnit.mul_left_eq_zero hu).mp h0

theorem idem_eq_one_of_not_mem [IsLocalRing L] {x : L} (hx : IsIdempotentElem x)
    (hm : x ∉ IsLocalRing.maximalIdeal L) : x = 1 := by
  have hu : IsUnit x := by
    by_contra h
    exact hm ((IsLocalRing.mem_maximalIdeal x).2 h)
  have h0 : x * (x - 1) = 0 := by rw [mul_sub, mul_one, hx.eq, sub_self]
  exact sub_eq_zero.mp ((IsUnit.mul_right_eq_zero hu).mp h0)

theorem idem_eq_zero_or_one [IsLocalRing L] {x : L} (hx : IsIdempotentElem x) : x = 0 ∨ x = 1 := by
  by_cases hm : x ∈ IsLocalRing.maximalIdeal L
  · exact Or.inl (idem_eq_zero_of_mem hx hm)
  · exact Or.inr (idem_eq_one_of_not_mem hx hm)

theorem idem_eq_one_of_apply_eq_one [IsLocalRing L] {O : Type*} [CommRing O] [Nontrivial O] [Algebra O L]
    (φ : L →ₐ[O] O) {x : L} (hx : IsIdempotentElem x) (h1 : φ x = 1) : x = 1 := by
  rcases idem_eq_zero_or_one hx with h | h
  · rw [h, map_zero] at h1; exact absurd h1 zero_ne_one
  · exact h

end Idem

section FiniteLocal

variable {A : Type*} [CommRing A] [IsLocalRing A] {S : Type*} [CommRing S] [Algebra A S] [Module.Finite A S]

theorem map_maximalIdeal_le_of_isMaximal (n : Ideal S) [hn : n.IsMaximal] :
    (IsLocalRing.maximalIdeal A).map (algebraMap A S) ≤ n := by
  have hint : Algebra.IsIntegral A S := inferInstance
  have hmax : (n.comap (algebraMap A S)).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal n
  have heq : n.comap (algebraMap A S) = IsLocalRing.maximalIdeal A := IsLocalRing.eq_maximalIdeal hmax
  rw [← heq]
  exact Ideal.map_comap_le

theorem map_maximalIdeal_le_jacobson :
    (IsLocalRing.maximalIdeal A).map (algebraMap A S) ≤ (⊥ : Ideal S).jacobson := by
  rw [Ideal.jacobson, le_sInf_iff]
  rintro n ⟨-, hn⟩
  exact map_maximalIdeal_le_of_isMaximal n

end FiniteLocal

section TensorLocal

variable (O : Type) [CommRing O] [IsLocalRing O]
variable (A : Type) [CommRing A] [Algebra O A] [Module.Finite O A] [IsLocalRing A]
variable (B : Type) [CommRing B] [Algebra O B] [Module.Finite O B] [IsLocalRing B]

theorem ker_le_maximalIdeal (ε : A →ₐ[O] O) : RingHom.ker ε ≤ IsLocalRing.maximalIdeal A :=
  IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top (ε : A →+* O))

theorem tmul_one_mem_jacobson {a : A} (ha : a ∈ IsLocalRing.maximalIdeal A) :
    a ⊗ₜ[O] (1 : B) ∈ (⊥ : Ideal (A ⊗[O] B)).jacobson := by
  have h := map_maximalIdeal_le_jacobson (A := A) (S := A ⊗[O] B)
  exact h (Ideal.mem_map_of_mem _ ha)

theorem one_tmul_mem_jacobson {b : B} (hb : b ∈ IsLocalRing.maximalIdeal B) :
    (1 : A) ⊗ₜ[O] b ∈ (⊥ : Ideal (A ⊗[O] B)).jacobson := by
  have h := tmul_one_mem_jacobson O B A (a := b) hb
  rw [Ideal.mem_jacobson_bot] at h ⊢
  intro y
  have hy := h ((Algebra.TensorProduct.comm O A B) y)
  have heq : (Algebra.TensorProduct.comm O A B) ((1 : A) ⊗ₜ[O] b * y + 1) =
      b ⊗ₜ[O] (1 : A) * (Algebra.TensorProduct.comm O A B) y + 1 := by
    rw [map_add, map_mul, map_one, Algebra.TensorProduct.comm_tmul]
  rw [← heq] at hy
  exact (isUnit_map_iff (Algebra.TensorProduct.comm O A B) _).mp hy

theorem isUnit_add_of_mem_jacobson {R : Type*} [CommRing R] {u j : R} (hu : IsUnit u)
    (hj : j ∈ (⊥ : Ideal R).jacobson) : IsUnit (u + j) := by
  obtain ⟨v, rfl⟩ := hu
  rw [Ideal.mem_jacobson_bot] at hj
  have h := hj ↑v⁻¹
  have : (j * ↑v⁻¹ + 1) * ↑v = ↑v + j := by
    rw [add_mul, mul_assoc, Units.inv_mul, mul_one, one_mul, add_comm]
  rw [← this]
  exact h.mul (Units.isUnit v)

theorem isLocalRing_tensorProduct (εA : A →ₐ[O] O) (εB : B →ₐ[O] O) : IsLocalRing (A ⊗[O] B) := by
  classical
  have hsA : Function.Surjective εA := fun r => ⟨algebraMap O A r, εA.commutes r⟩
  have hsB : Function.Surjective εB := fun r => ⟨algebraMap O B r, εB.commutes r⟩
  let ψ : A ⊗[O] B →ₐ[O] O := (Algebra.TensorProduct.lmul' O (S := O)).comp (Algebra.TensorProduct.map εA εB)

  have hlmul : ∀ w : O ⊗[O] O, Algebra.TensorProduct.lmul' O (S := O) w = TensorProduct.lid O O w := by
    intro w
    induction w with
    | zero => simp
    | tmul a b => rw [Algebra.TensorProduct.lmul'_apply_tmul, TensorProduct.lid_tmul, smul_eq_mul]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hinj : Function.Injective (Algebra.TensorProduct.lmul' O (S := O)) := by
    intro x y hxy
    rw [hlmul, hlmul] at hxy
    exact (TensorProduct.lid O O).injective hxy

  have hkerψ : RingHom.ker ψ = RingHom.ker (Algebra.TensorProduct.map εA εB) := by
    ext z
    simp only [RingHom.mem_ker]
    constructor
    · intro hz
      exact hinj (by rw [map_zero]; exact hz)
    · intro hz
      show Algebra.TensorProduct.lmul' O (S := O) (Algebra.TensorProduct.map εA εB z) = 0
      rw [hz, map_zero]
  have hker : RingHom.ker ψ ≤ (⊥ : Ideal (A ⊗[O] B)).jacobson := by
    rw [hkerψ, Algebra.TensorProduct.map_ker _ _ hsA hsB, sup_le_iff]
    constructor
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha
      exact tmul_one_mem_jacobson O A B (ker_le_maximalIdeal O A εA ha)
    · rw [Ideal.map_le_iff_le_comap]
      intro b hb
      exact one_tmul_mem_jacobson O A B (ker_le_maximalIdeal O B εB hb)

  have hlift : ∀ z : A ⊗[O] B, IsUnit (ψ z) → IsUnit z := by
    intro z hz
    have hsplit : z = algebraMap O (A ⊗[O] B) (ψ z) + (z - algebraMap O (A ⊗[O] B) (ψ z)) := by abel
    rw [hsplit]
    refine isUnit_add_of_mem_jacobson (hz.map _) (hker ?_)
    rw [RingHom.mem_ker, map_sub, AlgHom.commutes]
    exact sub_self _
  haveI : Nontrivial (A ⊗[O] B) := (ψ : A ⊗[O] B →+* O).domain_nontrivial
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun z => ?_
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (ψ z) with h | h
  · exact Or.inl (hlift z h)
  · refine Or.inr (hlift _ ?_)
    rwa [map_sub, map_one]

end TensorLocal

section Counit

variable {O : Type} [CommRing O] {C : Type} [CommRing C] [HopfAlgebra O C]

theorem lmul'_map_counit_counit_comul (c : C) :
    Algebra.TensorProduct.lmul' O (S := O)
      (Algebra.TensorProduct.map (Bialgebra.counitAlgHom O C) (Bialgebra.counitAlgHom O C) (Coalgebra.comul (R := O) c)) =
      Coalgebra.counit (R := O) c := by
  have hmap : ∀ z : C ⊗[O] C, Algebra.TensorProduct.map (Bialgebra.counitAlgHom O C) (Bialgebra.counitAlgHom O C) z =
      TensorProduct.map (Coalgebra.counit (R := O) (A := C)) (Coalgebra.counit (R := O) (A := C)) z := by
    intro z
    induction z with
    | zero => simp
    | tmul a b => rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  rw [hmap, ← LinearMap.rTensor_comp_lTensor, LinearMap.comp_apply, Coalgebra.lTensor_counit_comul,
    LinearMap.rTensor_tmul, Algebra.TensorProduct.lmul'_apply_tmul, mul_one]

end Counit

end ConnComp

open ConnComp HopfAlgebra in
theorem solution
    (p : ℕ) [Fact p.Prime]
    (O : Type) [CommRing O] [HenselianLocalRing O]
    [Algebra O (AlgebraicClosure ℚ)] [Algebra O (ZMod p)]
    (P : ValuationSubring (AlgebraicClosure ℚ))
    (hOP : ∀ x : O, algebraMap O (AlgebraicClosure ℚ) x ∈ P)
    (hloc : ∀ x : O, x ∈ IsLocalRing.maximalIdeal O →
      P.valuation (algebraMap O (AlgebraicClosure ℚ) x) < 1)
    (hres : ∀ x : O, algebraMap O (ZMod p) x = 0 ↔ x ∈ IsLocalRing.maximalIdeal O)
    (C : Type) [CommRing C] [HopfAlgebra O C] [Coalgebra.IsCocomm O C]
    [Module.Finite O C] [Module.Free O C] :
    ∃ (C₀ : Type) (_ : CommRing C₀) (_ : HopfAlgebra O C₀) (_ : Coalgebra.IsCocomm O C₀)
      (_ : Module.Finite O C₀) (_ : Module.Free O C₀)
      (q₀ : C →ₐc[O] C₀),
      Function.Surjective q₀ ∧

      IsLocalRing (ZMod p ⊗[O] C₀) ∧

      (∀ f : C →ₐ[O] AlgebraicClosure ℚ,
        (∀ c : C, P.valuation (f c - algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit c)) < 1) →
        ∃ g : C₀ →ₐ[O] AlgebraicClosure ℚ, f = g.comp (q₀ : C →ₐ[O] C₀)) ∧

      (∀ (L : Type) [CommRing L] [IsLocalRing L] [Algebra O L], IsLocalHom (algebraMap O L) →
        ∀ f : C →ₐ[O] L, (∀ c : C, f c - algebraMap O L (Coalgebra.counit c) ∈ IsLocalRing.maximalIdeal L) →
        ∃ g : C₀ →ₐ[O] L, f = g.comp (q₀ : C →ₐ[O] C₀)) ∧

      (∀ φ : C →ₐc[O] C, ∃! ψ : C₀ →ₐc[O] C₀, ψ.comp q₀ = q₀.comp φ) := by
  classical
  set εa : C →ₐ[O] O := Bialgebra.counitAlgHom O C with hεa
  have hεapp : ∀ c : C, εa c = Coalgebra.counit (R := O) c := fun c => rfl

  have hεsurj : Function.Surjective εa := fun r => ⟨algebraMap O C r, εa.commutes r⟩
  let m₀ : Ideal C := (IsLocalRing.maximalIdeal O).comap εa
  haveI hm₀ : m₀.IsMaximal := Ideal.comap_isMaximal_of_surjective (εa : C →+* O) hεsurj
  obtain ⟨hfin, eid, hCOI, hnot, hother, hlocq⟩ :=
    HenselianLocalRing.exists_completeOrthogonalIdempotents_forall_isLocalRing_quotient_of_moduleFinite (R := O) (S := C)
  let M₀ : MaximalSpectrum C := ⟨m₀, hm₀⟩
  set e : C := eid M₀ with he_def
  have he : IsIdempotentElem e := hCOI.idem M₀
  have heε : εa e = 1 := by
    have h1 : εa e ∉ IsLocalRing.maximalIdeal O := hnot M₀
    exact idem_eq_one_of_not_mem (he.map εa) h1

  set I : Ideal C := Ideal.span {1 - e} with hI
  haveI hC₀loc : IsLocalRing (C ⧸ I) := hlocq M₀
  have hmemI : ∀ {x : C}, x ∈ I ↔ ∃ c, x = c * (1 - e) := fun {x} => by
    rw [hI, Ideal.mem_span_singleton']; constructor <;> rintro ⟨c, hc⟩ <;> exact ⟨c, hc.symm⟩
  have hεI : ∀ x ∈ I, εa x = 0 := by
    intro x hx
    obtain ⟨c, rfl⟩ := hmemI.mp hx
    rw [map_mul, map_sub, map_one, heε, sub_self, mul_zero]

  let ε₀ : C ⧸ I →ₐ[O] O := Ideal.Quotient.liftₐ I εa hεI
  have hε₀ : ∀ c : C, ε₀ (Ideal.Quotient.mk I c) = εa c := fun c => rfl
  have hqe : Ideal.Quotient.mk I e = 1 := by
    rw [eq_comm, ← sub_eq_zero, ← map_one (Ideal.Quotient.mk I), ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl
  haveI : Module.Finite O (C ⧸ I) := inferInstance

  haveI hDloc : IsLocalRing ((C ⧸ I) ⊗[O] (C ⧸ I)) := isLocalRing_tensorProduct O (C ⧸ I) (C ⧸ I) ε₀ ε₀

  have hSI : antipode O (1 - e) ∈ I := by
    have hidem : IsIdempotentElem (Ideal.Quotient.mk I (antipode O e)) := by
      have := he.map (antipodeAlgHom O C)
      rw [antipodeAlgHom_apply] at this
      exact this.map (Ideal.Quotient.mk I)
    have h1 : Ideal.Quotient.mk I (antipode O e) = 1 := by
      refine idem_eq_one_of_apply_eq_one ε₀ hidem ?_
      rw [hε₀, hεapp, HopfAlgebra.counit_antipode, ← hεapp, heε]
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, HopfAlgebra.antipode_one, map_sub, map_one, h1, sub_self]
  have hΔI : Algebra.TensorProduct.map (Ideal.Quotient.mkₐ O I) (Ideal.Quotient.mkₐ O I)
      (Coalgebra.comul (R := O) (1 - e)) = 0 := by
    set y := Algebra.TensorProduct.map (Ideal.Quotient.mkₐ O I) (Ideal.Quotient.mkₐ O I) (Coalgebra.comul (R := O) e) with hy
    have hyidem : IsIdempotentElem y := by
      have : IsIdempotentElem (Bialgebra.comulAlgHom O C e) := he.map _
      exact this.map _
    have hy1 : y = 1 := by
      refine idem_eq_one_of_apply_eq_one ((Algebra.TensorProduct.lmul' O (S := O)).comp (Algebra.TensorProduct.map ε₀ ε₀)) hyidem ?_
      rw [hy, AlgHom.comp_apply, ← AlgHom.comp_apply (Algebra.TensorProduct.map ε₀ ε₀), ← Algebra.TensorProduct.map_comp]
      have hcomp : ε₀.comp (Ideal.Quotient.mkₐ O I) = εa := Ideal.Quotient.liftₐ_comp I εa hεI
      rw [hcomp, hεa, lmul'_map_counit_counit_comul, ← hεapp, heε]
    rw [map_sub, Bialgebra.comul_one, map_sub, map_one, ← hy, hy1, sub_self]
  haveI hHI : I.IsHopfIdeal' O :=
    { map_mkₐ_comul_eq_zero := by
        intro x hx
        obtain ⟨c, rfl⟩ := hmemI.mp hx
        have : Coalgebra.comul (R := O) (c * (1 - e)) = Coalgebra.comul (R := O) c * Coalgebra.comul (R := O) (1 - e) :=
          map_mul (Bialgebra.comulAlgHom O C) c (1 - e)
        rw [this, map_mul, hΔI, mul_zero]
      counit_eq_zero := hεI
      antipode_mem := by
        intro x hx
        obtain ⟨c, rfl⟩ := hmemI.mp hx
        have : antipode O (c * (1 - e)) = antipode O c * antipode O (1 - e) := map_mul (antipodeAlgHom O C) c (1 - e)
        rw [this]
        exact I.mul_mem_left _ hSI }

  have hIker : ∀ x ∈ I, e * x = 0 := by
    intro x hx
    obtain ⟨c, rfl⟩ := hmemI.mp hx
    rw [mul_comm c, ← mul_assoc, mul_sub, mul_one, he.eq, sub_self, zero_mul]
  let s' : (C ⧸ (I.restrictScalars O)) →ₗ[O] C :=
    (I.restrictScalars O).liftQ (LinearMap.mulLeft O e) (by
      intro x hx
      rw [LinearMap.mem_ker, LinearMap.mulLeft_apply]
      exact hIker x hx)
  let s : (C ⧸ I) →ₗ[O] C := s'.comp (Submodule.Quotient.restrictScalarsEquiv O I).symm.toLinearMap
  have hs : ∀ c : C, s (Ideal.Quotient.mk I c) = e * c := fun c => rfl
  let qₗ : C →ₗ[O] C ⧸ I := (Ideal.Quotient.mkₐ O I).toLinearMap
  have hsplit : qₗ.comp s = LinearMap.id := by
    apply LinearMap.ext
    intro z
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [LinearMap.comp_apply, hs, LinearMap.id_apply]
    show Ideal.Quotient.mk I (e * c) = Ideal.Quotient.mk I c
    rw [map_mul, hqe, one_mul]
  haveI : Module.Projective O (C ⧸ I) := Module.Projective.of_split s qₗ hsplit
  haveI : Module.Free O (C ⧸ I) := Module.free_of_flat_of_isLocalRing

  refine ⟨C ⧸ I, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    quotientBialgHom O I, quotientBialgHom_surjective O I, ?_, ?_, ?_, ?_⟩
  ·
    have hsurjO : Function.Surjective (algebraMap O (ZMod p)) := ZMod.ringHom_surjective _
    have hsurj : Function.Surjective (Algebra.TensorProduct.includeRight : (C ⧸ I) →ₐ[O] ZMod p ⊗[O] (C ⧸ I)) := by
      intro z
      induction z with
      | zero => exact ⟨0, map_zero _⟩
      | tmul r c =>
        obtain ⟨r', rfl⟩ := hsurjO r
        refine ⟨r' • c, ?_⟩
        rw [Algebra.TensorProduct.includeRight_apply, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def,
          mul_one]
      | add x y hx hy =>
        obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy
        exact ⟨a + b, map_add _ a b⟩
    haveI : Nontrivial (ZMod p ⊗[O] (C ⧸ I)) := by
      let τ : ZMod p ⊗[O] (C ⧸ I) →ₐ[O] ZMod p :=
        (Algebra.TensorProduct.lmul' O (S := ZMod p)).comp (Algebra.TensorProduct.map (AlgHom.id O (ZMod p))
          ((Algebra.ofId O (ZMod p)).comp ε₀))
      exact (τ : ZMod p ⊗[O] (C ⧸ I) →+* ZMod p).domain_nontrivial
    exact IsLocalRing.of_surjective' (Algebra.TensorProduct.includeRight : (C ⧸ I) →ₐ[O] ZMod p ⊗[O] (C ⧸ I)).toRingHom hsurj
  ·
    intro f hf
    have hfe : f (1 - e) = 0 := by
      have hidem : IsIdempotentElem (f (1 - e)) := (he.one_sub).map f
      rcases (IsIdempotentElem.iff_eq_zero_or_one.mp hidem) with h | h
      · exact h
      · exfalso
        have h0 : εa (1 - e) = 0 := by rw [map_sub, map_one, heε, sub_self]
        have := hf (1 - e)
        rw [h, ← hεapp, h0, map_zero, sub_zero, map_one] at this
        exact lt_irrefl _ this
    have hfI : ∀ x ∈ I, f x = 0 := by
      intro x hx
      obtain ⟨c, rfl⟩ := hmemI.mp hx
      rw [map_mul, hfe, mul_zero]
    refine ⟨Ideal.Quotient.liftₐ I f hfI, ?_⟩
    rw [quotientBialgHom_toAlgHom]
    exact (Ideal.Quotient.liftₐ_comp I f hfI).symm
  ·
    intro L _ _ _ hloch f hf
    have hfe : f (1 - e) = 0 := by
      have hidem : IsIdempotentElem (f (1 - e)) := (he.one_sub).map f
      have hm : f (1 - e) ∈ IsLocalRing.maximalIdeal L := by
        have h0 : εa (1 - e) = 0 := by rw [map_sub, map_one, heε, sub_self]
        have := hf (1 - e)
        rwa [← hεapp, h0, map_zero, sub_zero] at this
      exact idem_eq_zero_of_mem hidem hm
    have hfI : ∀ x ∈ I, f x = 0 := by
      intro x hx
      obtain ⟨c, rfl⟩ := hmemI.mp hx
      rw [map_mul, hfe, mul_zero]
    refine ⟨Ideal.Quotient.liftₐ I f hfI, ?_⟩
    rw [quotientBialgHom_toAlgHom]
    exact (Ideal.Quotient.liftₐ_comp I f hfI).symm
  ·
    intro φ
    have hφI : I ≤ I.comap (φ : C →ₐ[O] C) := by
      rw [hI, Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
      have hidem : IsIdempotentElem (Ideal.Quotient.mk I (φ e)) := (he.map φ).map _
      have h1 : Ideal.Quotient.mk I (φ e) = 1 := by
        refine idem_eq_one_of_apply_eq_one ε₀ hidem ?_
        rw [hε₀, hεapp, CoalgHomClass.counit_comp_apply, ← hεapp, heε]
      show (φ : C →ₐ[O] C) (1 - e) ∈ Ideal.span {1 - e}
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, map_sub, map_one]
      show 1 - Ideal.Quotient.mk I (φ e) = 0
      rw [h1, sub_self]
    let ψa : C ⧸ I →ₐ[O] C ⧸ I := Ideal.quotientMapₐ I (φ : C →ₐ[O] C) hφI
    have hψa : ψa.comp (Ideal.Quotient.mkₐ O I) = (Ideal.Quotient.mkₐ O I).comp (φ : C →ₐ[O] C) :=
      Ideal.quotient_map_comp_mkₐ I (φ : C →ₐ[O] C) hφI
    let ψ : C ⧸ I →ₐc[O] C ⧸ I :=
      BialgHom.ofAlgHom ψa
        (by
          refine Ideal.Quotient.algHom_ext O ?_
          rw [AlgHom.comp_assoc, hψa, ← AlgHom.comp_assoc, HopfIdealQuotient.counitAlgHom_eq,
            HopfIdealQuotient.counit_comp_mkₐ]
          apply AlgHom.ext; intro c
          exact CoalgHomClass.counit_comp_apply φ c)
        (by
          have hΔq : (Bialgebra.comulAlgHom O (C ⧸ I)).comp (Ideal.Quotient.mkₐ O I) =
              (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ O I) (Ideal.Quotient.mkₐ O I)).comp (Bialgebra.comulAlgHom O C) := by
            rw [HopfIdealQuotient.comulAlgHom_eq]
            exact HopfIdealQuotient.comul_comp_mkₐ O I
          have hφΔ : (Algebra.TensorProduct.map (φ : C →ₐ[O] C) (φ : C →ₐ[O] C)).comp (Bialgebra.comulAlgHom O C) =
              (Bialgebra.comulAlgHom O C).comp (φ : C →ₐ[O] C) := BialgHomClass.map_comp_comulAlgHom φ
          refine Ideal.Quotient.algHom_ext O ?_
          rw [AlgHom.comp_assoc, hΔq, ← AlgHom.comp_assoc, ← Algebra.TensorProduct.map_comp, hψa,
            Algebra.TensorProduct.map_comp, AlgHom.comp_assoc, hφΔ,
            ← AlgHom.comp_assoc, ← hΔq, AlgHom.comp_assoc, ← hψa, ← AlgHom.comp_assoc])
    refine ⟨ψ, ?_, ?_⟩
    · apply BialgHom.coe_algHom_injective
      exact hψa
    · intro ψ' hψ'
      apply BialgHom.coe_algHom_injective
      refine Ideal.Quotient.algHom_ext O ?_
      have := congrArg (fun f : C →ₐc[O] C ⧸ I => (f : C →ₐ[O] C ⧸ I)) hψ'
      rw [show ((ψ : C ⧸ I →ₐc[O] C ⧸ I) : C ⧸ I →ₐ[O] C ⧸ I).comp (Ideal.Quotient.mkₐ O I) =
        (Ideal.Quotient.mkₐ O I).comp (φ : C →ₐ[O] C) from hψa]
      exact this

end S_HopfAlgebra_exists_bialgHom_surjective_isLocalRing_tensorProduct_forall_point_comp_eq_of_henselianLocalRing
end P2MW
export P2MW.S_HopfAlgebra_exists_bialgHom_surjective_isLocalRing_tensorProduct_forall_point_comp_eq_of_henselianLocalRing (solution)
