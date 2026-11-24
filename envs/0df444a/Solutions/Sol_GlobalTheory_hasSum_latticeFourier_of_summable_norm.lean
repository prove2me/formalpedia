-- Prove2me | solution 1 for GlobalTheory.hasSum_latticeFourier_of_summable_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:23:44.384148+00:00
-- url     : https://prove2.me/submissions/bbf47a9d-9ce4-45eb-be1c-8a6be2563871

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LatticeFourierOfContDiffFiniteDimensional
import Theorems.Thm_GlobalTheory_covolume_eq_volume_latticeCell
import Theorems.Thm_GlobalTheory_norm_cexp_two_pi_I
import Theorems.Thm_GlobalTheory_latticeFourierCoeff_clm
import Theorems.Thm_GlobalTheory_average_fundamentalDomain_eq_cube
import Theorems.Thm_GlobalTheory_exists_equiv_innerDual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory Module Set
open scoped RealInnerProductSpace Real Pointwise ContDiff
noncomputable section
namespace GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
local notation "e[" t "]" => Complex.exp (2 * (π : ℂ) * Complex.I * ((t : ℝ) : ℂ))
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
local notation "L*" => LinearMap.BilinForm.dualSubmodule (innerₗ E) L
variable {L}
private theorem hasSum_latticeFourier_complex {A : E → ℂ} (hA : ∀ x ∈ L, Function.Periodic A x)
    (hc : Continuous A) (hs : Summable fun ν : L* ↦ latticeFourierCoeff L A ν) (y : E) :
    HasSum (fun ν : L* ↦ e[⟪(ν : E), y⟫] • latticeFourierCoeff L A ν) (A y) := by
  set b := Free.chooseBasis ℤ L
  set b₀ := b.ofZLatticeBasis ℝ L
  obtain ⟨-, -, φ, hφ⟩ := exists_equiv_innerDual L b
  set p : (Free.ChooseBasisIndex ℤ L → ℝ) → UnitAddTorus (Free.ChooseBasisIndex ℤ L) :=
    fun x i ↦ (x i : UnitAddCircle) with hp
  have hq : IsOpenQuotientMap p :=
    IsOpenQuotientMap.piMap fun _ ↦ QuotientAddGroup.isOpenQuotientMap_mk
  set f₀ : UnitAddTorus (Free.ChooseBasisIndex ℤ L) → ℂ :=
    fun z ↦ A (b₀.equivFun.symm (Function.surjInv hq.surjective z)) with hf₀
  have hfp : ∀ x, f₀ (p x) = A (b₀.equivFun.symm x) := fun x ↦ by
    set x' := Function.surjInv hq.surjective (p x)
    have h1 : p x' = p x := Function.surjInv_eq _ _
    have h2 : b₀.equivFun.symm (x' - x) ∈ L := by
      rw [Basis.equivFun_symm_apply]
      refine sum_mem fun i _ ↦ ?_
      have h3 : ((x' i - x i : ℝ) : UnitAddCircle) = 0 := by
        rw [AddCircle.coe_sub, sub_eq_zero]; exact congrFun h1 i
      obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff _).1 h3
      rw [Pi.sub_apply, ← hn, smul_assoc, one_smul]
      exact L.smul_mem n (by simp [b₀])
    rw [← hA _ h2 (b₀.equivFun.symm x), ← map_add, add_sub_cancel]
  let f : C(UnitAddTorus (Free.ChooseBasisIndex ℤ L), ℂ) := ⟨f₀,
    hq.isQuotientMap.continuous_iff.2 <| by
      rw [show f₀ ∘ p = A ∘ b₀.equivFunL.symm from funext hfp]; fun_prop⟩
  have hchar : ∀ n x, UnitAddTorus.mFourier n (p x) = e[∑ i, n i * x i] := fun n x ↦ by
    simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, hp, fourier_coe_apply,
      ← Complex.exp_sum]
    congr 1
    push_cast
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  have hcoeff : ∀ n, UnitAddTorus.mFourierCoeff f n = latticeFourierCoeff L A (φ n) := fun n ↦ by
    rw [UnitAddTorus.mFourierCoeff_eq_integral f n 0, latticeFourierCoeff,
      covolume_eq_volume_latticeCell, latticeCell, average_fundamentalDomain_eq_cube]
    simp only [Pi.zero_apply, zero_add]
    refine integral_congr_ae (.of_forall fun x ↦ ?_)
    change UnitAddTorus.mFourier (-n) (p x) • f₀ (p x) = _
    simp only [hchar, hfp]
    congr 4
    refine Eq.trans ?_ (congrArg Neg.neg (hφ n x).symm)
    simp
  have hsum := UnitAddTorus.hasSum_mFourier_series_apply_of_summable (f := f)
    (by rw [funext hcoeff]; exact φ.summable_iff.2 hs) (p (b₀.equivFun y))
  rw [← φ.hasSum_iff]
  change HasSum _ (f₀ (p _)) at hsum
  simp only [hfp, hchar, hcoeff, ← hφ] at hsum
  simpa only [b₀, LinearEquiv.symm_apply_apply, smul_eq_mul, mul_comm, Function.comp_def]
    using hsum
end GlobalTheory
end
end

set_option autoImplicit false
open MeasureTheory Module Set
open scoped RealInnerProductSpace Real Pointwise ContDiff
noncomputable section
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
local notation "e[" t "]" => Complex.exp (2 * (π : ℂ) * Complex.I * ((t : ℝ) : ℂ))
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
local notation "L*" => LinearMap.BilinForm.dualSubmodule (innerₗ E) L
variable {L}
namespace GlobalTheory
theorem _root_.solution [CompleteSpace V] {A : E → V}
    (hA : ∀ x ∈ L, Function.Periodic A x) (hc : Continuous A)
    (hs : Summable fun ν : L* ↦ ‖latticeFourierCoeff L A ν‖) (y : E) :
    HasSum (fun ν : L* ↦ e[⟪(ν : E), y⟫] • latticeFourierCoeff L A ν) (A y) := by
  have h1 : Summable fun ν : L* ↦ e[⟪(ν : E), y⟫] • latticeFourierCoeff L A ν :=
    .of_norm (by simpa only [norm_smul, norm_cexp_two_pi_I, one_mul] using hs)
  convert h1.hasSum using 1
  refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2 fun T ↦ ?_
  have h2 := hasSum_latticeFourier_complex (L := L) (A := fun b ↦ T (A b))
    (fun x hx b ↦ by simp only [hA x hx b]) (by fun_prop)
    (by simpa only [latticeFourierCoeff_clm T hc, Function.comp_def] using hs.of_norm.map T T.continuous) y
  simp only [latticeFourierCoeff_clm T hc, ← map_smul] at h2
  exact h2.unique (T.hasSum h1.hasSum)
end GlobalTheory
