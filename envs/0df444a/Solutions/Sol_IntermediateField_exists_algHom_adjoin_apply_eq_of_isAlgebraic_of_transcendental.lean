-- Prove2me | solution 1 for IntermediateField.exists_algHom_adjoin_apply_eq_of_isAlgebraic_of_transcendental
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/e8ae0b0e-3dbd-5b1c-90f3-fce06fe2d3c1

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IntermediateField_exists_algHom_adjoin_apply_eq_of_isAlgebraic_of_transcendental

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open Polynomial

namespace AdjoinExt

variable {K L L' : Type*} [Field K] [Field L] [Algebra K L] [Field L'] [Algebra K L']

section Span

variable (G : Set L) (h1 : (1 : L) ∈ G) (hmul : ∀ x ∈ G, ∀ y ∈ G, x * y ∈ G)

def monoid : Submonoid L where
  carrier := G
  mul_mem' := fun {x y} hx hy => hmul x hx y hy
  one_mem' := h1

include h1 hmul in
theorem adjoin_toSubmodule : Subalgebra.toSubmodule (Algebra.adjoin K G) = Submodule.span K G := by
  rw [Algebra.adjoin_eq_span]
  congr 1
  exact congrArg SetLike.coe (Submonoid.closure_eq (monoid G h1 hmul))

def Φ₁ : (G →₀ K) →ₗ[K] L := Finsupp.linearCombination K (fun x : G => (x : L))

def Φ₂ (θ : L → L') : (G →₀ K) →ₗ[K] L' := Finsupp.linearCombination K (fun x : G => θ x)

theorem range_Φ₁ : LinearMap.range (Φ₁ (K := K) G) = Submodule.span K G := by
  rw [Φ₁, Finsupp.range_linearCombination, Subtype.range_coe]

variable {G}

theorem Φ₁_apply (l : G →₀ K) : Φ₁ G l = l.sum fun x r => r • (x : L) := Finsupp.linearCombination_apply _ _

theorem Φ₂_apply (θ : L → L') (l : G →₀ K) : Φ₂ (K := K) G θ l = l.sum fun x r => r • θ x :=
  Finsupp.linearCombination_apply _ _

theorem ker_le (θ : L → L')
    (hlin : ∀ c : L →₀ K, (↑c.support : Set L) ⊆ G →
      (c.sum fun x r => r • x) = 0 → (c.sum fun x r => r • θ x) = 0) :
    LinearMap.ker (Φ₁ (K := K) G) ≤ LinearMap.ker (Φ₂ G θ) := by
  classical
  intro l hl
  rw [LinearMap.mem_ker] at hl ⊢
  have hsupp : (↑(l.mapDomain (Subtype.val : G → L)).support : Set L) ⊆ G := by
    intro x hx
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support (Finset.mem_coe.mp hx))
    exact y.2
  have e1 : ((l.mapDomain (Subtype.val : G → L)).sum fun x r => r • x) = Φ₁ G l := by
    rw [Finsupp.sum_mapDomain_index_inj Subtype.val_injective, Φ₁_apply]
  have e2 : ((l.mapDomain (Subtype.val : G → L)).sum fun x r => r • θ x) = Φ₂ G θ l := by
    rw [Finsupp.sum_mapDomain_index_inj Subtype.val_injective, Φ₂_apply]
  have := hlin _ hsupp (by rw [e1, hl])
  rwa [e2] at this

set_option maxHeartbeats 4000000 in

def ψ (θ : L → L') (hker : LinearMap.ker (Φ₁ (K := K) G) ≤ LinearMap.ker (Φ₂ (K := K) G θ)) :
    LinearMap.range (Φ₁ (K := K) G) →ₗ[K] L' :=
  let e : LinearMap.range (Φ₁ (K := K) G) →ₗ[K] (G →₀ K) ⧸ LinearMap.ker (Φ₁ (K := K) G) :=
    (Φ₁ (K := K) G).quotKerEquivRange.symm.toLinearMap
  let q : ((G →₀ K) ⧸ LinearMap.ker (Φ₁ (K := K) G)) →ₗ[K] L' :=
    (LinearMap.ker (Φ₁ (K := K) G)).liftQ (Φ₂ (K := K) G θ) hker
  q.comp e

set_option maxHeartbeats 4000000 in
theorem ψ_apply (θ : L → L') (hker : LinearMap.ker (Φ₁ (K := K) G) ≤ LinearMap.ker (Φ₂ (K := K) G θ))
    (l : G →₀ K) (h : Φ₁ G l ∈ LinearMap.range (Φ₁ (K := K) G)) :
    ψ θ hker ⟨Φ₁ G l, h⟩ = Φ₂ G θ l := by
  rw [ψ, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearMap.quotKerEquivRange_symm_apply_image,
    Submodule.mkQ_apply, Submodule.liftQ_apply]

end Span

section Main

variable (K)

theorem main {L L' : Type*} [Field L] [Algebra K L] [Field L'] [Algebra K L']
    (G : Set L) (h1 : (1 : L) ∈ G) (hmul : ∀ x ∈ G, ∀ y ∈ G, x * y ∈ G)
    (θ : L → L') (hθ : ∀ x ∈ G, ∀ y ∈ G, θ (x * y) = θ x * θ y)
    (hlin : ∀ c : L →₀ K, (↑c.support : Set L) ⊆ G →
      (c.sum fun x r => r • x) = 0 → (c.sum fun x r => r • θ x) = 0)
    (F : IntermediateField K L) (hF : F = IntermediateField.adjoin K G)
    (x₀ : F) (hx₀G : (x₀ : L) ∈ G) (hx₀ : Transcendental K (θ x₀))
    (halg : Algebra.IsAlgebraic (IntermediateField.adjoin K ({x₀} : Set F)) F) :
    ∃ Θ : F →ₐ[K] L', ∀ x : F, (x : L) ∈ G → Θ x = θ x := by
  classical
  subst hF

  set A : Subalgebra K L := Algebra.adjoin K G with hAdef
  have hAspan : Subalgebra.toSubmodule A = Submodule.span K G := adjoin_toSubmodule G h1 hmul
  have hker := ker_le (K := K) (G := G) θ hlin
  have hAV : ∀ {x : L}, x ∈ A → x ∈ LinearMap.range (Φ₁ (K := K) G) := by
    intro x hx
    rw [range_Φ₁, ← hAspan]
    exact hx
  set ψA : A →ₗ[K] L' :=
    { toFun := fun a => ψ θ hker ⟨a, hAV a.2⟩
      map_add' := fun a b => by rw [← map_add]; rfl
      map_smul' := fun c a => by rw [RingHom.id_apply, ← map_smul]; rfl } with hψAdef
  have hψA : ∀ a : A, ψA a = ψ θ hker ⟨a, hAV a.2⟩ := fun a => rfl

  have hgen : ∀ (x : L) (hx : x ∈ G), ψA ⟨x, Algebra.subset_adjoin hx⟩ = θ x := by
    intro x hx
    have e : (⟨x, hAV (Algebra.subset_adjoin hx)⟩ : LinearMap.range (Φ₁ (K := K) G)) =
        ⟨Φ₁ G (Finsupp.single ⟨x, hx⟩ 1), LinearMap.mem_range_self _ _⟩ := by
      apply Subtype.ext
      simp [Φ₁]
    rw [hψA, e, ψ_apply, Φ₂, Finsupp.linearCombination_single, one_smul]

  set s : Set A := {a | (a : L) ∈ G} with hsdef
  have hs : Submodule.span K s = ⊤ := by
    apply Submodule.map_injective_of_injective (f := (Subalgebra.toSubmodule A).subtype) Subtype.val_injective
    rw [Submodule.map_span, Submodule.map_top]
    conv_rhs => rw [Submodule.range_subtype, hAspan]
    congr 1
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩; exact ha
    · intro hx; exact ⟨⟨x, Algebra.subset_adjoin hx⟩, hx, rfl⟩
  have hmulψ : ∀ a b : A, ψA (a * b) = ψA a * ψA b := by
    set B₁ : A →ₗ[K] A →ₗ[K] L' := (LinearMap.mul K A).compr₂ ψA with hB₁
    set B₂ : A →ₗ[K] A →ₗ[K] L' := ((LinearMap.mul K L').comp ψA).compl₂ ψA with hB₂
    have hB : B₁ = B₂ := by
      refine LinearMap.ext_on hs (fun a ha => LinearMap.ext_on hs (fun b hb => ?_))
      simp only [hB₁, hB₂, LinearMap.compr₂_apply, LinearMap.mul_apply', LinearMap.compl₂_apply,
        LinearMap.comp_apply]
      have hab : ((a * b : A) : L) ∈ G := hmul _ ha _ hb
      have ea : a = ⟨(a : L), Algebra.subset_adjoin ha⟩ := Subtype.ext rfl
      have eb : b = ⟨(b : L), Algebra.subset_adjoin hb⟩ := Subtype.ext rfl
      have eab : a * b = ⟨((a * b : A) : L), Algebra.subset_adjoin hab⟩ := Subtype.ext rfl
      rw [eab, hgen _ hab, ea, eb, hgen _ ha, hgen _ hb]
      exact hθ _ ha _ hb
    intro a b
    have := congrArg (fun B : A →ₗ[K] A →ₗ[K] L' => B a b) hB
    simpa only [hB₁, hB₂, LinearMap.compr₂_apply, LinearMap.mul_apply', LinearMap.compl₂_apply,
      LinearMap.comp_apply] using this

  have hθ1 : θ 1 = 1 := by
    have h2 : θ 1 * θ 1 = θ 1 := by rw [← hθ 1 h1 1 h1, mul_one]
    rcases mul_eq_zero.mp (show θ 1 * (θ 1 - 1) = 0 by rw [mul_sub, mul_one, h2, sub_self]) with h | h
    · exfalso
      apply hx₀
      have : θ x₀ = 0 := by rw [← mul_one (x₀ : L), hθ _ hx₀G _ h1, h, mul_zero]
      rw [this]
      exact isAlgebraic_zero
    · exact sub_eq_zero.mp h
  have honeψ : ψA 1 = 1 := by
    have e : (1 : A) = ⟨1, Algebra.subset_adjoin h1⟩ := Subtype.ext rfl
    rw [e, hgen 1 h1, hθ1]
  set ΘA : A →ₐ[K] L' := AlgHom.ofLinearMap ψA honeψ hmulψ with hΘAdef
  have hΘA : ∀ a : A, ΘA a = ψA a := fun a => rfl

  set x₀A : A := ⟨(x₀ : L), Algebra.subset_adjoin hx₀G⟩ with hx₀A
  have hΘx₀ : ΘA x₀A = θ x₀ := by rw [hΘA, hx₀A, hgen _ hx₀G]

  have hinj : Function.Injective ΘA := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra hne

    have haF : (a : L) ∈ IntermediateField.adjoin K G := IntermediateField.algebra_adjoin_le_adjoin K G a.2
    set y : IntermediateField.adjoin K G := ⟨a, haF⟩ with hydef
    have hy0 : y ≠ 0 := by
      intro e
      have h' := congrArg Subtype.val e
      exact hne (Subtype.ext h')
    set E : IntermediateField K (IntermediateField.adjoin K G) :=
      IntermediateField.adjoin K ({x₀} : Set (IntermediateField.adjoin K G)) with hEdef
    set R₀ : Subalgebra K (IntermediateField.adjoin K G) :=
      Algebra.adjoin K ({x₀} : Set (IntermediateField.adjoin K G)) with hR₀def
    open scoped IntermediateField.algebraAdjoinAdjoin in
    have key : ∃ q' : Polynomial R₀, q'.coeff 0 ≠ 0 ∧ Polynomial.aeval y q' = 0 := by
      have hyint : IsIntegral E y := (halg.isAlgebraic y).isIntegral
      have hq0 : (minpoly E y).coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hyint hy0
      obtain ⟨b, hb, hbq⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R₀) (minpoly E y)
      refine ⟨IsLocalization.integerNormalization (nonZeroDivisors R₀) (minpoly E y), ?_,
        IsLocalization.integerNormalization_aeval_eq_zero _ (minpoly E y) (minpoly.aeval E y)⟩
      intro h0
      have hc := congrArg (fun p => Polynomial.coeff p 0) hbq
      simp only [Polynomial.coeff_map, Polynomial.coeff_smul, h0, map_zero] at hc
      rw [Algebra.smul_def] at hc
      exact mul_ne_zero ((map_ne_zero_iff _ (IsFractionRing.injective R₀ E)).mpr (nonZeroDivisors.ne_zero hb))
        hq0 hc.symm
    obtain ⟨q', hq'0, hq'y⟩ := key

    have hcoef : ∀ i, ∃ r : Polynomial K, ((q'.coeff i : R₀) : IntermediateField.adjoin K G) =
        Polynomial.aeval x₀ r := fun i => by
      have hm : ((q'.coeff i : R₀) : IntermediateField.adjoin K G) ∈
          Algebra.adjoin K ({x₀} : Set (IntermediateField.adjoin K G)) := (q'.coeff i).2
      rw [Algebra.adjoin_singleton_eq_range_aeval] at hm
      obtain ⟨r, hr⟩ := hm
      exact ⟨r, hr.symm⟩
    choose r hr using hcoef

    set d : ℕ := q'.natDegree + 1 with hd
    set zA : A := ∑ i ∈ Finset.range d, Polynomial.aeval x₀A (r i) * a ^ i with hzA
    have hzA0 : zA = 0 := by
      apply Subtype.ext
      have h2 : (IntermediateField.adjoin K G).val (Polynomial.aeval y q') = 0 := by rw [hq'y, map_zero]
      rw [Polynomial.aeval_eq_sum_range, ← hd] at h2
      show A.val zA = ((0 : A) : L)
      rw [ZeroMemClass.coe_zero, ← h2, hzA, map_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, map_pow, ← Polynomial.aeval_algHom_apply, Algebra.smul_def, map_mul, map_pow]
      congr 1
      rw [hx₀A]
      change Polynomial.aeval (x₀ : L) (r i) =
        (IntermediateField.adjoin K G).val ((q'.coeff i : R₀) : IntermediateField.adjoin K G)
      rw [hr i, ← Polynomial.aeval_algHom_apply]
      rfl
    have h3 := congrArg ΘA hzA0
    rw [map_zero, hzA, map_sum] at h3
    simp only [map_mul, map_pow, ha] at h3
    rw [Finset.sum_eq_single 0 (fun i _ hi => by rw [zero_pow hi, mul_zero])
      (fun h => absurd (Finset.mem_range.mpr (Nat.succ_pos _)) h), pow_zero, mul_one,
      ← Polynomial.aeval_algHom_apply, hΘx₀] at h3

    have hr0 : r 0 = 0 := by
      by_contra hr0
      exact hx₀ ⟨r 0, hr0, h3⟩
    apply hq'0
    apply Subtype.ext
    rw [hr 0, hr0, map_zero]
    rfl

  open scoped IntermediateField.algebraAdjoinAdjoin in
  refine ⟨IsFractionRing.liftAlgHom (A := A) (K := IntermediateField.adjoin K G) hinj, fun x hx => ?_⟩
  open scoped IntermediateField.algebraAdjoinAdjoin in
  have e : x = algebraMap A (IntermediateField.adjoin K G) ⟨x, Algebra.subset_adjoin hx⟩ := Subtype.ext rfl
  open scoped IntermediateField.algebraAdjoinAdjoin in
  rw [e, IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap]
  exact hgen _ hx

end Main

end AdjoinExt

theorem solution
    (K : Type*) {L L' : Type*} [Field K] [Field L] [Algebra K L] [Field L'] [Algebra K L']
    (G : Set L) (h1 : (1 : L) ∈ G) (hmul : ∀ x ∈ G, ∀ y ∈ G, x * y ∈ G)
    (θ : L → L') (hθ : ∀ x ∈ G, ∀ y ∈ G, θ (x * y) = θ x * θ y)
    (hlin : ∀ c : L →₀ K, (↑c.support : Set L) ⊆ G →
      (c.sum fun x r => r • x) = 0 → (c.sum fun x r => r • θ x) = 0)
    (F : IntermediateField K L) (hF : F = IntermediateField.adjoin K G)
    (x₀ : F) (hx₀G : (x₀ : L) ∈ G) (hx₀ : Transcendental K (θ x₀))
    (halg : Algebra.IsAlgebraic (IntermediateField.adjoin K ({x₀} : Set F)) F) :
    ∃ Θ : F →ₐ[K] L', ∀ x : F, (x : L) ∈ G → Θ x = θ x :=
  AdjoinExt.main K G h1 hmul θ hθ hlin F hF x₀ hx₀G hx₀ halg

end
end S_IntermediateField_exists_algHom_adjoin_apply_eq_of_isAlgebraic_of_transcendental
end P2MW
export P2MW.S_IntermediateField_exists_algHom_adjoin_apply_eq_of_isAlgebraic_of_transcendental (solution)
