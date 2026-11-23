-- Prove2me | solution 1 for GlobalTheory.SmGL.MultiIrr.smInd_stages
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:22:47.626125+00:00
-- url     : https://prove2.me/submissions/980bf1b6-5776-40fa-a96c-bc2dae4a3b5d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BernsteinUnitaryProductIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantModulus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LowerEquivUpperSwap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsIrreducibleIffOfLinearEquiv
import Theorems.Thm_GlobalTheory_SmGL_MultiIrr_eq_zero_of_ev
import Theorems.Thm_GlobalTheory_SmGL_MultiIrr_exists_tensor
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel Matrix
open scoped TensorProduct
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.MultiIrr
variable {F G H M V W U : Type} [Field F] [Group G] [Group H] [Group M] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W] [AddCommGroup U] [Module F U]
variable [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace H] [IsTopologicalGroup H]
namespace GlobalTheory.SmGL.MultiIrr
theorem _root_.solution {P Q : Subgroup G} (hPQ : P ≤ Q) {P' : Subgroup H} (π : Q →* M × H) (j : H →* Q)
    (hj : Continuous fun x => (j x : G)) (hπj : ∀ x, π (j x) = (1, x))
    (hP : ∀ q : Q, (q : G) ∈ P ↔ (π q).2 ∈ P') {K : Set H} (hK : IsCompact K)
    (hPK : ∀ x, ∃ p : P', ∃ w ∈ K, x = p * w) (D : M × H →* Fˣ)
    (hD : ∀ᶠ u in nhds (1 : H), D (1, u) = 1)
    (σ₀ : Representation F M V) (ρ : Representation F P' W) (σ : Representation F P U)
    (κ : V ⊗[F] W ≃ₗ[F] U)
    (hσ : ∀ (q : Q) (h1 : (q : G) ∈ P) (h2 : (π q).2 ∈ P') x, σ ⟨q, h1⟩ (κ x) =
      (D (π q) : F) • κ (TensorProduct.map (σ₀ (π q).1) (ρ ⟨_, h2⟩) x))
    (τ : Representation F Q (V ⊗[F] smoothPart (ind P' ρ)))
    (hτ : ∀ q x, τ q x = (D (π q) : F) • TensorProduct.map (σ₀ (π q).1) (smInd P' ρ (π q).2) x) :
    Nonempty ((smInd Q τ).Equiv (smInd P σ)) := by
  let ε : V ⊗[F] smoothPart (ind P' ρ) →ₗ[F] U := κ.toLinearMap ∘ₗ (ev ρ 1).lTensor V
  have hε : ∀ (q : Q) (h1 : (q : G) ∈ P) t, σ ⟨q, h1⟩ (ε t) = ε (τ q t) := by
    intro q h1 t
    show σ _ (κ _) = κ _
    rw [hσ q h1 ((hP q).1 h1), hτ, map_smul, map_smul]
    congr 2
    induction t with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul v f =>
      simp only [LinearMap.lTensor_tmul, TensorProduct.map_tmul]
      congr 1
      show _ = f.1.1 (1 * (π q).2)
      exact (f.1.2 ⟨_, (hP q).1 h1⟩ 1).symm.trans (by rw [one_mul, mul_one])
  have hεj : ∀ x t, ε (τ (j x) t) = (D (1, x) : F) • κ ((ev ρ x).lTensor V t) := by
    intro x t
    show κ _ = _
    rw [hτ, hπj, map_smul, map_smul]
    congr 2
    induction t with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul v f =>
      simp only [LinearMap.lTensor_tmul, TensorProduct.map_tmul, map_one, Module.End.one_apply]
      congr 1
      show f.1.1 (1 * x) = f.1.1 x
      rw [one_mul]
  have inj : ∀ t t', (∀ q, ε (τ q t) = ε (τ q t')) → t = t' := fun t t' h =>
    sub_eq_zero.1 (eq_zero_of_ev ρ _ fun x => by
      have := h (j x)
      rw [hεj, hεj] at this
      rw [map_sub, κ.injective (smul_right_injective U (D (1, x)).ne_zero this), sub_self])
  have surj : ∀ f : smoothPart (ind P σ), ∃ t, ∀ q : Q, ε (τ q t) = f.1.1 q := by
    intro f
    obtain ⟨t, ht⟩ := exists_tensor ρ hK hPK (fun x => (D (1, x) : F)⁻¹ • κ.symm (f.1.1 (j x)))
      (fun p x => by
        have h2 : (π (j p)).2 ∈ P' := by rw [hπj]; exact p.2
        have h3 := f.1.2 ⟨j p, (hP _).2 h2⟩ (j x)
        have h4 := hσ (j p) ((hP _).2 h2) h2 (κ.symm (f.1.1 (j x)))
        simp only [hπj, map_one, LinearEquiv.apply_symm_apply] at h4
        have h5 : D (1, (p : H) * x) = D (1, (p : H)) * D (1, x) := by rw [← map_mul]; simp
        simp only [map_mul, Subgroup.coe_mul, h5]
        rw [h3, h4, map_smul, map_smul, κ.symm_apply_apply, smul_smul]
        congr 1
        simp only [Units.val_mul]
        field_simp)
      (by
        filter_upwards [hD, (hj.tendsto' 1 1 (by simp)).eventually (eventually_of_smooth f)] with u h1 h2 x
        have h5 : D (1, x * u) = D (1, x) * D (1, u) := by rw [← map_mul]; simp
        simp only [map_mul, Subgroup.coe_mul, h5, h1, mul_one, h2])
    refine ⟨t, fun q => ?_⟩
    have hp : ((q * (j (π q).2)⁻¹ : Q) : G) ∈ P := (hP _).2 (by simp [hπj])
    have hq : q = (q * (j (π q).2)⁻¹) * j (π q).2 := by simp
    conv_lhs => rw [hq, map_mul, Module.End.mul_apply, ← hε _ hp, hεj, ht]
    conv_rhs => rw [hq, Subgroup.coe_mul]
    rw [f.1.2 ⟨_, hp⟩]
    simp [smul_smul]
  let Ψ : smoothPart (ind Q τ) →ₗ[F] smoothPart (ind P σ) :=
    indPull (MonoidHom.id G) continuous_id ε fun p => ⟨⟨p, hPQ p.2⟩, rfl, hε ⟨p, hPQ p.2⟩ p.2⟩
  refine ⟨Representation.IntertwiningMap.ofBijective ⟨Ψ, fun g => rfl⟩ ⟨?_, fun f => ?_⟩⟩
  · intro f f' h
    refine Subtype.ext (Subtype.ext (funext fun x => inj _ _ fun q => ?_))
    rw [← f.1.2, ← f'.1.2]
    exact congrFun (congrArg (fun φ => φ.1.1) h) (q * x)
  · choose t ht using fun g => surj (smInd P σ g f)
    have ht' : ∀ g (q : Q), ε (τ q (t g)) = f.1.1 (q * g) := ht
    refine ⟨⟨⟨t, fun q g => inj _ _ fun q' => ?_⟩, mem_smooth_of_eventually _
      ((eventually_of_smooth f).mono fun u hu x => inj _ _ fun q => ?_)⟩,
      Subtype.ext (Subtype.ext (funext fun x => ?_))⟩
    · rw [← Module.End.mul_apply, ← map_mul, ht', ht', Subgroup.coe_mul, mul_assoc]
    · show ε (τ q (t (x * u))) = ε (τ q (t x))
      rw [ht', ht', ← mul_assoc, hu]
    · show ε (t x) = _
      simpa using ht' x 1
end GlobalTheory.SmGL.MultiIrr
