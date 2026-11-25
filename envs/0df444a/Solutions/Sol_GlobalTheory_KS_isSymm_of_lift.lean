-- Prove2me | solution 1 for GlobalTheory.KS.isSymm_of_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:18:17.870923+00:00
-- url     : https://prove2.me/submissions/ec181ec7-a995-4f42-804d-5ed563ed6628

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsHolomorphicUniformisationPowerThetaKeyDatu
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ThetaCocyclePeriodicNonvanishingSectionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_KodairaSpencerClassIsSymmOfLift
import Theorems.Thm_GlobalTheory_KS_ex_add_lattice
import Theorems.Thm_GlobalTheory_KS_isHolFamily_ex_comp
import Theorems.Thm_GlobalTheory_KS_exists_frame_on_family
import Theorems.Thm_GlobalTheory_KS_PtDer_log_cocycle
import Theorems.Thm_GlobalTheory_PowUnif_exists_chart
import Theorems.Thm_GlobalTheory_T_theta_cocycle_periodic_nonvanishing_sections

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KS
variable {g : ℕ} {A₀ : Over (Sp ℂ)} [GrpObj A₀] {L₀ : LB A₀.left} (u : HolUnif A₀ L₀ g) {X : Scheme.{0}}
private theorem top_le_preimage_inf_iff_and {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (A B : X.Opens) :
    ⊤ ≤ x ⁻¹ᵁ (A ⊓ B) ↔ ⊤ ≤ x ⁻¹ᵁ A ∧ ⊤ ≤ x ⁻¹ᵁ B := by
  show ⊤ ≤ x ⁻¹ᵁ A ⊓ x ⁻¹ᵁ B ↔ _
  exact le_inf_iff
private theorem valAt'_val_unit_ne_zero {X : Scheme.{0}} (y : Sp ℂ ⟶ X) {W : X.Opens} (hW : ⊤ ≤ y ⁻¹ᵁ W)
    (f : (Γ(X, W))ˣ) : valAt' y W f.val ≠ 0 := by
  have h1 : valAt' y W (f.val * f.inv) = valAt' y W f.val * valAt' y W f.inv := by
    unfold valAt'
    simp only [dif_pos hW]
    unfold valAt
    simp only [map_mul]
  have h2 : valAt' y W (1 : Γ(X, W)) = 1 := by
    unfold valAt'
    simp only [dif_pos hW]
    unfold valAt
    simp only [map_one]
  intro h0
  rw [f.val_inv, h2, h0, zero_mul] at h1
  exact one_ne_zero h1
end GlobalTheory.KS
end
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
open GlobalTheory GlobalTheory.KS
variable {g : ℕ} {A₀ : Over (Sp ℂ)} [GrpObj A₀] {L₀ : LB A₀.left} (u : HolUnif A₀ L₀ g) {X : Scheme.{0}}
namespace GlobalTheory.KS
theorem _root_.solution : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap x₀) → ∀ D Θ s, KSRel u p m D Θ s → ∀ L : LB X, L.IsLB → LBIso P₀.L (L.pull m) → IsSymm Hm Θ := by
  intro P₀ u Hm χ hG R _ x₀ X p m hp hpb D Θ s hks L hL hw
  obtain ⟨a, ha1, ha2, ha3⟩ := exists_frame_on_family u P₀.isLB m L hL hw
  have hhol := isHolFamily_ex_comp u m
  have hopen : ∀ W : X.Opens, IsOpen (dom u m W) := fun W => (hhol W 0).1
  have hfn : ∀ (W : X.Opens) (f : Γ(X, W)), DifferentiableOn ℂ (fn u m W f) (dom u m W) :=
    fun W f => (hhol W f).2
  have hdom : ∀ A B : X.Opens, dom u m (A ⊓ B) = dom u m A ∩ dom u m B := by
    intro A B
    ext z
    exact top_le_preimage_inf_iff_and _ _ _
  have hfnper : ∀ (W : X.Opens) (f : Γ(X, W)) (z : Fin P₀.g → ℂ) (l : u.Λ),
      fn u m W f (z + l) = fn u m W f z := by
    intro W f z l
    unfold fn
    rw [ex_add_lattice]
  have key := _root_.GlobalTheory.T.theta_cocycle_periodic_nonvanishing_sections P₀.g u.Λ u.discrete u.full Hm Θ L.ι (fun i => dom u m (L.U i)) a
    (fun i j z => s z (L.U i ⊓ L.U j) (L.g i j).val / fn u m (L.U i ⊓ L.U j) (L.g i j).val z)
    (fun l => χ l * Complex.exp (↑Real.pi / 2 * ((l : Fin P₀.g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin P₀.g → ℂ)))))
    (fun i => hopen _)
    (by
      intro i l z hz
      show ⊤ ≤ ((u.ex (z + l)).left ≫ m) ⁻¹ᵁ L.U i
      rw [ex_add_lattice]
      exact hz)
    (fun z => PowUnif.exists_chart hL ((u.ex z).left ≫ m))
    ha1
    (by
      intro i l z hz
      refine ha3 i l z _ hz fun b hb => ?_
      rw [hG.ah.2.2.2 l b z hb, Complex.exp_add]
      ring)
    (by
      intro i j
      rw [← hdom]
      have h1 : DifferentiableOn ℂ (fun z => s z (L.U i ⊓ L.U j) (L.g i j).val) (dom u m (L.U i ⊓ L.U j)) :=
        hks.hol _ _
      have h2 : DifferentiableOn ℂ (fn u m (L.U i ⊓ L.U j) (L.g i j).val) (dom u m (L.U i ⊓ L.U j)) := hfn _ _
      have h3 : ∀ z ∈ dom u m (L.U i ⊓ L.U j), fn u m (L.U i ⊓ L.U j) (L.g i j).val z ≠ 0 :=
        fun z hz => valAt'_val_unit_ne_zero _ hz _
      refine (h1.mul (h2.inv h3)).congr fun z _ => ?_
      exact div_eq_mul_inv _ _)
    (by
      intro i j k z hz
      obtain ⟨⟨hi, hj⟩, hk⟩ := hz
      exact PtDer.log_cocycle (hks.der z) hL i j k hi hj hk)
    (by
      intro i j l z hz
      have hzW : z ∈ dom u m (L.U i ⊓ L.U j) := by
        rw [hdom]
        exact hz
      have hs := hks.per l (L.U i ⊓ L.U j) (L.g i j).val z hzW
      show s (z + l) (L.U i ⊓ L.U j) (L.g i j).val / fn u m (L.U i ⊓ L.U j) (L.g i j).val (z + l) = _
      rw [hs, hfnper]
      have hdf : DifferentiableAt ℂ (fn u m (L.U i ⊓ L.U j) (L.g i j).val) z :=
        (hfn _ _).differentiableAt ((hopen _).mem_nhds hzW)
      have hda : DifferentiableAt ℂ (a j) z := (ha1 j).1.differentiableAt ((hopen _).mem_nhds hz.2)
      have hEq : fderiv ℂ (a i) z = fderiv ℂ (fun y => fn u m (L.U i ⊓ L.U j) (L.g i j).val y * a j y) z := by
        apply Filter.EventuallyEq.fderiv_eq
        filter_upwards [(hopen _).mem_nhds hzW] with y hy
        rw [hdom] at hy
        exact ha2 i j y hy
      have nf : fn u m (L.U i ⊓ L.U j) (L.g i j).val z ≠ 0 := valAt'_val_unit_ne_zero _ hzW _
      have na : a j z ≠ 0 := (ha1 j).2 z hz.2
      rw [hEq, fderiv_fun_mul hdf hda, ha2 i j z hz]
      simp only [FunLike.coe_add, FunLike.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
      ring)
  intro z w
  unfold hermForm
  exact key z w
end GlobalTheory.KS
