-- Prove2me | solution 1 for HopfAlgebra.exists_comul_quotient_bijective_of_completeOrthogonalIdempotents_of_counit_apply_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/a70d6a00-d4d0-576b-bdcd-6dcb8b3ee120

import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import Theorems.Thm_HopfAlgebra_isHopfGalois_of_surjective
import Theorems.Thm_IsLocalRing_tensorProduct_of_moduleFinite_of_isAlgClosed_residueField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_comul_quotient_bijective_of_completeOrthogonalIdempotents_of_counit_apply_eq_one

set_option autoImplicit false

open scoped TensorProduct

namespace TorsorDecompE95

variable {R : Type} [CommRing R]

theorem isIdempotentElem_eq_zero_or_one {S : Type*} [CommRing S] [IsLocalRing S] {x : S}
    (hx : IsIdempotentElem x) : x = 0 ∨ x = 1 := by
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self x with h | h
  · right
    have : x * x = x * 1 := by rw [mul_one]; exact hx
    exact (h.mul_right_injective this)
  · left
    have h1 : (1 - x) * x = 0 := by rw [sub_mul, one_mul, hx, sub_self]
    have : (1 - x) * x = (1 - x) * 0 := by rw [h1, mul_zero]
    exact h.mul_right_injective this

theorem existsUnique_eq_one_of_completeOrthogonalIdempotents {S : Type*} [CommRing S] [IsLocalRing S]
    {ι : Type*} [Fintype ι] {f : ι → S} (hf : CompleteOrthogonalIdempotents f) :
    ∃! l, f l = 1 := by
  classical
  have hex : ∃ l, f l ≠ 0 := by
    by_contra h
    push Not at h
    have : (∑ l, f l) = 0 := Finset.sum_eq_zero (fun l _ => h l)
    rw [hf.complete] at this
    exact one_ne_zero this
  obtain ⟨l, hl⟩ := hex
  have hl1 : f l = 1 := (isIdempotentElem_eq_zero_or_one (hf.idem l)).resolve_left hl
  refine ⟨l, hl1, fun l' hl' => ?_⟩
  by_contra hne
  have := hf.ortho hne
  simp only [hl1, hl', mul_one] at this
  exact one_ne_zero this

theorem eq_zero_of_ne_of_completeOrthogonalIdempotents {S : Type*} [CommRing S] [IsLocalRing S]
    {ι : Type*} [Fintype ι] {f : ι → S} (hf : CompleteOrthogonalIdempotents f)
    {l l' : ι} (hl : f l = 1) (hne : l' ≠ l) : f l' = 0 := by
  rcases isIdempotentElem_eq_zero_or_one (hf.idem l') with h | h
  · exact h
  · exact absurd ((existsUnique_eq_one_of_completeOrthogonalIdempotents hf).unique h hl) hne

section COI

variable {H : Type} [CommRing H] [Algebra R H]
variable {ι : Type} [Fintype ι] {e : ι → H}

omit [Fintype ι] in
theorem mk_self_eq_one (e : ι → H) (j : ι) :
    Ideal.Quotient.mk (Ideal.span {1 - e j}) (e j) = 1 := by
  rw [eq_comm, ← sub_eq_zero, ← map_one (Ideal.Quotient.mk _), ← map_sub,
    Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span rfl

theorem mk_eq_zero_of_ne (he : CompleteOrthogonalIdempotents e) {j k : ι} (h : k ≠ j) :
    Ideal.Quotient.mk (Ideal.span {1 - e j}) (e k) = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  refine ⟨e k, ?_⟩
  have h' : e j * e k = 0 := he.ortho (Ne.symm h)
  rw [sub_mul, one_mul, h', sub_zero]

theorem mk_eq_zero_iff (he : CompleteOrthogonalIdempotents e) (j : ι) (x : H) :
    Ideal.Quotient.mk (Ideal.span {1 - e j}) x = 0 ↔ e j * x = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    rw [← mul_assoc, mul_sub, mul_one, (he.idem j).eq, sub_self, zero_mul]
  · intro hx
    refine ⟨x, ?_⟩
    rw [sub_mul, one_mul, hx, sub_zero]

end COI

section Tensor

variable {H : Type} [CommRing H] [Algebra R H]
variable {ι : Type} [Fintype ι] {e : ι → H}

local notation "Q[" e "," j "]" => _ ⧸ Ideal.span {1 - e j}

noncomputable abbrev qq (e : ι → H) (j : ι) : H →ₐ[R] H ⧸ Ideal.span {1 - e j} :=
  Ideal.Quotient.mkₐ R (Ideal.span {1 - e j})

omit [Fintype ι] in
theorem qq_apply (e : ι → H) (j : ι) (x : H) :
    qq (R := R) e j x = Ideal.Quotient.mk (Ideal.span {1 - e j}) x := rfl

omit [Fintype ι] in
theorem qq_surjective (e : ι → H) (j : ι) : Function.Surjective (qq (R := R) e j) :=
  Ideal.Quotient.mkₐ_surjective R _

theorem map_qq_eq_zero_iff (he : CompleteOrthogonalIdempotents e) (j k : ι) (x : H ⊗[R] H) :
    Algebra.TensorProduct.map (qq (R := R) e j) (qq (R := R) e k) x = 0 ↔
      (e j ⊗ₜ[R] e k) * x = 0 := by
  constructor
  · intro hx
    have hmem : x ∈ RingHom.ker (Algebra.TensorProduct.map (qq (R := R) e j) (qq (R := R) e k)) :=
      hx
    rw [Algebra.TensorProduct.map_ker (hf := qq_surjective e j) (hg := qq_surjective e k)] at hmem

    let J : Ideal (H ⊗[R] H) := Ideal.span {1 - e j ⊗ₜ[R] e k}
    have hann : ∀ y ∈ J, (e j ⊗ₜ[R] e k) * y = 0 := by
      intro y hy
      rw [Ideal.mem_span_singleton] at hy
      obtain ⟨c, rfl⟩ := hy
      have hE : IsIdempotentElem (e j ⊗ₜ[R] e k) := by
        change (e j ⊗ₜ[R] e k) * (e j ⊗ₜ[R] e k) = e j ⊗ₜ[R] e k
        rw [Algebra.TensorProduct.tmul_mul_tmul, (he.idem j).eq, (he.idem k).eq]
      rw [← mul_assoc, mul_sub, mul_one, hE.eq, sub_self, zero_mul]
    have hle : (RingHom.ker (qq (R := R) e j)).map
          (Algebra.TensorProduct.includeLeft : H →ₐ[R] H ⊗[R] H) ⊔
        (RingHom.ker (qq (R := R) e k)).map
          (Algebra.TensorProduct.includeRight : H →ₐ[R] H ⊗[R] H) ≤ J := by
      refine sup_le ?_ ?_
      · rw [Ideal.map_le_iff_le_comap]
        intro y hy
        rw [RingHom.mem_ker, qq_apply, mk_eq_zero_iff he] at hy
        rw [Ideal.mem_comap, Ideal.mem_span_singleton]
        refine ⟨y ⊗ₜ[R] 1, ?_⟩
        change y ⊗ₜ[R] (1 : H) = _
        rw [sub_mul, one_mul, Algebra.TensorProduct.tmul_mul_tmul, hy, TensorProduct.zero_tmul, sub_zero]
      · rw [Ideal.map_le_iff_le_comap]
        intro y hy
        rw [RingHom.mem_ker, qq_apply, mk_eq_zero_iff he] at hy
        rw [Ideal.mem_comap, Ideal.mem_span_singleton]
        refine ⟨1 ⊗ₜ[R] y, ?_⟩
        change (1 : H) ⊗ₜ[R] y = _
        rw [sub_mul, one_mul, Algebra.TensorProduct.tmul_mul_tmul, hy, TensorProduct.tmul_zero, sub_zero]
    exact hann x (hle hmem)
  · intro hx
    have h1 : Algebra.TensorProduct.map (qq (R := R) e j) (qq (R := R) e k) (e j ⊗ₜ[R] e k) = 1 := by
      rw [Algebra.TensorProduct.map_tmul, qq_apply, qq_apply, mk_self_eq_one, mk_self_eq_one]
      rfl
    have : x = (1 - e j ⊗ₜ[R] e k) * x + (e j ⊗ₜ[R] e k) * x := by ring
    rw [this, hx, add_zero, map_mul, map_sub, map_one, h1, sub_self, zero_mul]

theorem free_quotient_of_completeOrthogonalIdempotents [IsLocalRing R] [Module.Finite R H]
    [Module.Free R H] (he : CompleteOrthogonalIdempotents e) (k : ι) :
    Module.Free R (H ⧸ Ideal.span {1 - e k}) := by
  classical
  let π : H →ₗ[R] (∀ l : ι, H ⧸ Ideal.span {1 - e l}) :=
    LinearMap.pi fun l => (qq (R := R) e l).toLinearMap
  have hπ : Function.Bijective π := he.bijective_pi
  let πe : H ≃ₗ[R] (∀ l : ι, H ⧸ Ideal.span {1 - e l}) := LinearEquiv.ofBijective π hπ
  haveI : Module.Free R (∀ l : ι, H ⧸ Ideal.span {1 - e l}) := Module.Free.of_equiv πe
  haveI : Module.Finite R (H ⧸ Ideal.span {1 - e k}) :=
    Module.Finite.of_surjective (qq (R := R) e k).toLinearMap (qq_surjective (R := R) e k)
  haveI : Module.Projective R (H ⧸ Ideal.span {1 - e k}) :=
    Module.Projective.of_split
      (LinearMap.single R (fun l : ι => H ⧸ Ideal.span {1 - e l}) k)
      (LinearMap.proj k) (LinearMap.proj_comp_single_same R _ k)
  exact Module.free_of_flat_of_isLocalRing

end Tensor

section Hopf

variable {H : Type} [CommRing H] [HopfAlgebra R H]

theorem canAlgHom_id_tmul (a b : H) :
    HopfAlgebra.canAlgHom (BialgHom.id R H) (a ⊗ₜ[R] b) =
      (a ⊗ₜ[R] (1 : H)) * Coalgebra.comul (R := R) b := by
  rw [HopfAlgebra.canAlgHom_tmul, HopfAlgebra.coaction_apply, BialgHom.id_toAlgHom,
    Algebra.TensorProduct.map_id]
  rfl

theorem canAlgHom_id_one_tmul (b : H) :
    HopfAlgebra.canAlgHom (BialgHom.id R H) (1 ⊗ₜ[R] b) = Coalgebra.comul (R := R) b := by
  rw [canAlgHom_id_tmul, ← Algebra.TensorProduct.one_def, one_mul]

theorem canAlgHom_id_tmul_one (a : H) :
    HopfAlgebra.canAlgHom (BialgHom.id R H) (a ⊗ₜ[R] 1) = a ⊗ₜ[R] 1 := by
  rw [canAlgHom_id_tmul, Bialgebra.comul_one, mul_one]

theorem eq_algebraMap_counit_of_mem_hopfKer_id {h : H}
    (hh : h ∈ HopfAlgebra.hopfKer (BialgHom.id R H)) :
    h = algebraMap R H (Coalgebra.counit (R := R) h) := by
  rw [HopfAlgebra.mem_hopfKer_iff, HopfAlgebra.coaction_apply, BialgHom.id_toAlgHom,
    Algebra.TensorProduct.map_id] at hh
  change Coalgebra.comul (R := R) h = h ⊗ₜ[R] 1 at hh
  have h2 := Coalgebra.rTensor_counit_comul (R := R) h
  rw [hh, LinearMap.rTensor_tmul] at h2

  have h3 := congrArg (TensorProduct.lid R H) h2
  rw [TensorProduct.lid_tmul, TensorProduct.lid_tmul, one_smul] at h3
  rw [Algebra.algebraMap_eq_smul_one]
  exact h3.symm

theorem canMap_id_bijective [Module.Finite R H] [Module.Free R H] :
    Function.Bijective (HopfAlgebra.canAlgHom (BialgHom.id R H)) := by
  have hG := HopfAlgebra.isHopfGalois_of_surjective (BialgHom.id R H) Function.surjective_id
  refine ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro z hz
    have hmem := hG.2 z hz
    have hbot : Submodule.span R (HopfAlgebra.balancingRelations (BialgHom.id R H)) = ⊥ := by
      rw [Submodule.span_eq_bot]
      rintro x ⟨a, h, a', hh, rfl⟩
      rw [eq_algebraMap_counit_of_mem_hopfKer_id hh, ← Algebra.smul_def, mul_comm,
        ← Algebra.smul_def, TensorProduct.smul_tmul, sub_self]
    rw [hbot, Submodule.mem_bot] at hmem
    exact hmem
  · exact hG.1

end Hopf

end TorsorDecompE95

open TorsorDecompE95 in

theorem solution
    (R : Type) [CommRing R] [IsLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)]
    (H : Type) [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Flat R H]
    (ι : Type) [Fintype ι] (e : ι → H) (he : CompleteOrthogonalIdempotents e)
    (hloc : ∀ i : ι, IsLocalRing (H ⧸ Ideal.span {1 - e i}))
    (i₀ : ι) (h₀ : Coalgebra.counit (R := R) (e i₀) = 1) :
    ∀ i : ι,
      Module.Free R (H ⧸ Ideal.span {1 - e i}) ∧
      Module.FaithfullyFlat R (H ⧸ Ideal.span {1 - e i}) ∧
      Module.finrank R (H ⧸ Ideal.span {1 - e i}) = Module.finrank R (H ⧸ Ideal.span {1 - e i₀}) ∧
      ∃ ρ : (H ⧸ Ideal.span {1 - e i}) →ₐ[R] (H ⧸ Ideal.span {1 - e i}) ⊗[R] (H ⧸ Ideal.span {1 - e i₀}),
        ρ.comp (Ideal.Quotient.mkₐ R (Ideal.span {1 - e i})) =
          (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R (Ideal.span {1 - e i})) (Ideal.Quotient.mkₐ R (Ideal.span {1 - e i₀}))).comp
            (Bialgebra.comulAlgHom R H) ∧
        Function.Bijective
          (Algebra.TensorProduct.lift
            (Algebra.TensorProduct.includeLeft :
              (H ⧸ Ideal.span {1 - e i}) →ₐ[R] (H ⧸ Ideal.span {1 - e i}) ⊗[R] (H ⧸ Ideal.span {1 - e i₀}))
            ρ (fun _ _ => Commute.all _ _)) ∧
        ∀ (L : Type) [CommRing L] [Algebra R L]
          (t : (H ⧸ Ideal.span {1 - e i}) →ₐ[R] L) (w : (H ⧸ Ideal.span {1 - e i₀}) →ₐ[R] L),
          ((Algebra.TensorProduct.lift t w (fun _ _ => Commute.all _ _)).comp ρ).comp
              (Ideal.Quotient.mkₐ R (Ideal.span {1 - e i})) =
            (WithConv.toConv (t.comp (Ideal.Quotient.mkₐ R (Ideal.span {1 - e i}))) *
              WithConv.toConv (w.comp (Ideal.Quotient.mkₐ R (Ideal.span {1 - e i₀})))).ofConv := by

  classical

  haveI : Module.Free R H := Module.free_of_flat_of_isLocalRing
  set I : ι → Ideal H := fun j => Ideal.span {1 - e j} with hI
  let q : ∀ j : ι, H →ₐ[R] H ⧸ Ideal.span {1 - e j} := fun j => Ideal.Quotient.mkₐ R _
  have hq : ∀ j, q j = qq (R := R) e j := fun j => rfl
  haveI hfinQ : ∀ j : ι, Module.Finite R (H ⧸ Ideal.span {1 - e j}) := fun j =>
    Module.Finite.of_surjective (q j).toLinearMap (Ideal.Quotient.mkₐ_surjective R _)
  haveI hlocQQ : ∀ j k : ι, IsLocalRing ((H ⧸ Ideal.span {1 - e j}) ⊗[R] (H ⧸ Ideal.span {1 - e k})) :=
    fun j k => IsLocalRing.tensorProduct_of_moduleFinite_of_isAlgClosed_residueField R _ _

  let F : ∀ j k : ι, H →ₐ[R] (H ⧸ Ideal.span {1 - e j}) ⊗[R] (H ⧸ Ideal.span {1 - e k}) :=
    fun j k => (Algebra.TensorProduct.map (q j) (q k)).comp (Bialgebra.comulAlgHom R H)
  have hF : ∀ j k x, F j k x = Algebra.TensorProduct.map (q j) (q k) (Coalgebra.comul (R := R) x) :=
    fun j k x => rfl
  have hFcoi : ∀ j k, CompleteOrthogonalIdempotents ((F j k) ∘ e) := fun j k =>
    he.map (F j k).toRingHom

  have hμex : ∀ j k, ∃! l, F j k (e l) = 1 := fun j k =>
    existsUnique_eq_one_of_completeOrthogonalIdempotents (hFcoi j k)
  let μ : ι → ι → ι := fun j k => (hμex j k).exists.choose
  have hμ : ∀ j k, F j k (e (μ j k)) = 1 := fun j k => (hμex j k).exists.choose_spec
  have hμ0 : ∀ j k l, l ≠ μ j k → F j k (e l) = 0 := fun j k l hl =>
    eq_zero_of_ne_of_completeOrthogonalIdempotents (hFcoi j k) (hμ j k) hl

  have hvan : ∀ j k l, l ≠ μ j k → (e j ⊗ₜ[R] e k) * Coalgebra.comul (R := R) (e l) = 0 := by
    intro j k l hl
    rw [← map_qq_eq_zero_iff he, ← hq, ← hq, ← hF]
    exact hμ0 j k l hl

  let β := HopfAlgebra.canAlgHom (BialgHom.id R H)
  have hβ : Function.Bijective β := canMap_id_bijective

  have hμsurj : ∀ j, Function.Surjective (μ j) := by
    intro j l
    by_contra hcon
    push Not at hcon
    have h1 : (e j ⊗ₜ[R] (1 : H)) * Coalgebra.comul (R := R) (e l) = 0 := by
      have : (e j ⊗ₜ[R] (1 : H)) = ∑ k, e j ⊗ₜ[R] e k := by
        rw [← TensorProduct.tmul_sum, he.complete]
      rw [this, Finset.sum_mul]
      exact Finset.sum_eq_zero fun k _ => hvan j k l (fun h => hcon k h.symm)
    have h2 : β (e j ⊗ₜ[R] e l) = 0 := by
      change HopfAlgebra.canAlgHom (BialgHom.id R H) (e j ⊗ₜ[R] e l) = 0
      rw [canAlgHom_id_tmul, h1]
    have h3 : e j ⊗ₜ[R] e l = 0 := (injective_iff_map_eq_zero β).mp hβ.1 _ h2
    have h4 : Algebra.TensorProduct.map (q j) (q l) (e j ⊗ₜ[R] e l) = 1 := by
      rw [Algebra.TensorProduct.map_tmul]
      change Ideal.Quotient.mk _ (e j) ⊗ₜ[R] Ideal.Quotient.mk _ (e l) = 1
      rw [mk_self_eq_one, mk_self_eq_one]; rfl
    rw [h3, map_zero] at h4
    exact zero_ne_one h4
  have hμinj : ∀ j, Function.Injective (μ j) := fun j =>
    Finite.injective_iff_surjective.mpr (hμsurj j)

  have hεI : ∀ a ∈ Ideal.span {1 - e i₀}, Bialgebra.counitAlgHom R H a = 0 := by
    intro a ha
    rw [Ideal.mem_span_singleton] at ha
    obtain ⟨c, rfl⟩ := ha
    rw [map_mul, map_sub, map_one, Bialgebra.counitAlgHom_apply, h₀, sub_self, zero_mul]
  let εq : (H ⧸ Ideal.span {1 - e i₀}) →ₐ[R] R := Ideal.Quotient.liftₐ _ (Bialgebra.counitAlgHom R H) hεI
  have hεq : ∀ x, εq (q i₀ x) = Coalgebra.counit (R := R) x := fun x => rfl
  have hμi₀ : ∀ j, μ j i₀ = j := by
    intro j
    by_contra hne
    have h0 : F j i₀ (e j) = 0 := hμ0 j i₀ j (fun h => hne h.symm)

    have hG : ∀ x, Algebra.TensorProduct.rid R R (H ⧸ Ideal.span {1 - e j})
        (Algebra.TensorProduct.map (AlgHom.id R _) εq (F j i₀ x)) = q j x := by
      intro x
      let 𝓡 := Coalgebra.Repr.arbitrary R x
      have h5 := congrArg (TensorProduct.rid R H) (Coalgebra.sum_tmul_counit_eq (R := R) 𝓡)
      simp only [map_sum, TensorProduct.rid_tmul, one_smul] at h5
      rw [hF, ← 𝓡.eq, map_sum, map_sum, map_sum]
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hεq, Algebra.TensorProduct.rid_tmul]
      conv_rhs => rw [← h5, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul]
    have := hG (e j)
    rw [h0, map_zero, map_zero] at this
    have h1 : q j (e j) = 1 := mk_self_eq_one e j
    rw [h1] at this
    exact zero_ne_one this

  intro j

  have hFI : ∀ a ∈ Ideal.span {1 - e j}, F j i₀ a = 0 := by
    intro a ha
    rw [Ideal.mem_span_singleton] at ha
    obtain ⟨c, rfl⟩ := ha
    have : F j i₀ (e j) = 1 := by rw [← hμi₀ j]; exact (hμi₀ j).symm ▸ hμ j i₀
    rw [map_mul, map_sub, map_one, this, sub_self, zero_mul]
  let ρ : (H ⧸ Ideal.span {1 - e j}) →ₐ[R]
      (H ⧸ Ideal.span {1 - e j}) ⊗[R] (H ⧸ Ideal.span {1 - e i₀}) :=
    Ideal.Quotient.liftₐ _ (F j i₀) hFI
  have hρ : ρ.comp (q j) = F j i₀ := Ideal.Quotient.liftₐ_comp _ _ _
  have hρ' : ∀ x, ρ (q j x) = F j i₀ x := fun x => rfl

  let T : (H ⧸ Ideal.span {1 - e j}) ⊗[R] (H ⧸ Ideal.span {1 - e j}) →ₐ[R]
      (H ⧸ Ideal.span {1 - e j}) ⊗[R] (H ⧸ Ideal.span {1 - e i₀}) :=
    Algebra.TensorProduct.lift
      (Algebra.TensorProduct.includeLeft :
        (H ⧸ Ideal.span {1 - e j}) →ₐ[R] (H ⧸ Ideal.span {1 - e j}) ⊗[R] (H ⧸ Ideal.span {1 - e i₀}))
      ρ (fun _ _ => Commute.all _ _)
  have hT : T.comp (Algebra.TensorProduct.map (q j) (q j)) =
      (Algebra.TensorProduct.map (q j) (q i₀)).comp β := by
    apply Algebra.TensorProduct.ext'
    intro a b
    change T (q j a ⊗ₜ[R] q j b) =
      Algebra.TensorProduct.map (q j) (q i₀) (HopfAlgebra.canAlgHom (BialgHom.id R H) (a ⊗ₜ[R] b))
    rw [Algebra.TensorProduct.lift_tmul, canAlgHom_id_tmul, map_mul, Algebra.TensorProduct.map_tmul,
      map_one, hρ', hF]
    rfl
  have hT' : ∀ z, T (Algebra.TensorProduct.map (q j) (q j) z) =
      Algebra.TensorProduct.map (q j) (q i₀) (β z) := fun z => congr($hT z)
  have hTsurj : Function.Surjective T := by
    intro w
    obtain ⟨y, rfl⟩ := Algebra.TensorProduct.map_surjective (q j) (q i₀)
      (Ideal.Quotient.mkₐ_surjective R _) (Ideal.Quotient.mkₐ_surjective R _) w
    obtain ⟨z, rfl⟩ := hβ.2 y
    exact ⟨_, hT' z⟩
  have hTinj : Function.Injective T := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    obtain ⟨z, rfl⟩ := Algebra.TensorProduct.map_surjective (q j) (q j)
      (Ideal.Quotient.mkₐ_surjective R _) (Ideal.Quotient.mkₐ_surjective R _) w

    set z' := (e j ⊗ₜ[R] e j) * z with hz'
    have hE1 : Algebra.TensorProduct.map (q j) (q j) (e j ⊗ₜ[R] e j) = 1 := by
      rw [Algebra.TensorProduct.map_tmul]
      change Ideal.Quotient.mk _ (e j) ⊗ₜ[R] Ideal.Quotient.mk _ (e j) = 1
      rw [mk_self_eq_one]; rfl
    have hzz' : Algebra.TensorProduct.map (q j) (q j) z = Algebra.TensorProduct.map (q j) (q j) z' := by
      rw [hz', map_mul, hE1, one_mul]
    rw [hzz'] at hw ⊢

    have hA : (e j ⊗ₜ[R] e i₀) * β z' = 0 := by
      rw [← map_qq_eq_zero_iff he, ← hq, ← hq, ← hT' z']
      exact hw

    have hB : ∀ k, k ≠ i₀ → (e j ⊗ₜ[R] e k) * β z' = 0 := by
      intro k hk
      have hz1 : z' = z' * ((1 : H) ⊗ₜ[R] e j) := by
        rw [hz', mul_comm ((e j ⊗ₜ[R] e j) * z), ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul,
          one_mul, (he.idem j).eq]
      have hne : j ≠ μ j k := by
        intro h
        apply hk
        apply hμinj j
        rw [← h, hμi₀]
      rw [hz1, map_mul]
      change (e j ⊗ₜ[R] e k) * (β z' * HopfAlgebra.canAlgHom (BialgHom.id R H) (1 ⊗ₜ[R] e j)) = 0
      rw [canAlgHom_id_one_tmul, mul_left_comm, hvan j k j hne, mul_zero]

    have hC : β z' = (e j ⊗ₜ[R] (1 : H)) * β z' := by
      have hz2 : z' = (e j ⊗ₜ[R] (1 : H)) * z' := by
        rw [hz', ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul, (he.idem j).eq]
      conv_lhs => rw [hz2]
      rw [map_mul]
      change HopfAlgebra.canAlgHom (BialgHom.id R H) (e j ⊗ₜ[R] 1) * β z' = _
      rw [canAlgHom_id_tmul_one]
    have hD : β z' = 0 := by
      rw [hC]
      have : (e j ⊗ₜ[R] (1 : H)) = ∑ k, e j ⊗ₜ[R] e k := by
        rw [← TensorProduct.tmul_sum, he.complete]
      rw [this, Finset.sum_mul]
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hk : k = i₀
      · subst hk; exact hA
      · exact hB k hk
    have : z' = 0 := (injective_iff_map_eq_zero β).mp hβ.1 _ hD
    rw [this, map_zero]
  have hTbij : Function.Bijective T := ⟨hTinj, hTsurj⟩

  have hfree : ∀ k : ι, Module.Free R (H ⧸ Ideal.span {1 - e k}) := fun k =>
    free_quotient_of_completeOrthogonalIdempotents (R := R) he k
  haveI := hfree
  have hff : Module.FaithfullyFlat R (H ⧸ Ideal.span {1 - e j}) := inferInstance

  have hrank : Module.finrank R (H ⧸ Ideal.span {1 - e j}) =
      Module.finrank R (H ⧸ Ideal.span {1 - e i₀}) := by
    have h1 := (LinearEquiv.ofBijective T.toLinearMap hTbij).finrank_eq
    rw [Module.finrank_tensorProduct, Module.finrank_tensorProduct] at h1
    have hpos : 0 < Module.finrank R (H ⧸ Ideal.span {1 - e j}) :=
      (Module.finrank_pos_iff_of_free R _).mpr inferInstance
    exact Nat.eq_of_mul_eq_mul_left hpos h1

  refine ⟨hfree j, hff, hrank, ρ, hρ, hTbij, ?_⟩

  intro L _ _ t w
  apply AlgHom.ext
  intro x
  have hR := (Coalgebra.Repr.arbitrary R x).eq
  rw [AlgHom.convMul_def]
  simp only [AlgHom.comp_apply]
  rw [hρ', hF, Bialgebra.comulAlgHom_apply, ← hR]
  simp only [map_sum, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul,
    Algebra.TensorProduct.lmul'_apply_tmul, AlgHom.comp_apply]
  rfl

end S_HopfAlgebra_exists_comul_quotient_bijective_of_completeOrthogonalIdempotents_of_counit_apply_eq_one
end P2MW
export P2MW.S_HopfAlgebra_exists_comul_quotient_bijective_of_completeOrthogonalIdempotents_of_counit_apply_eq_one (solution)
