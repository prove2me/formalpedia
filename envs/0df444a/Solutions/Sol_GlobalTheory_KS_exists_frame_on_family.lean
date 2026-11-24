-- Prove2me | solution 1 for GlobalTheory.KS.exists_frame_on_family
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:32:27.031489+00:00
-- url     : https://prove2.me/submissions/fc61dd25-94a5-4800-a820-00ad7e39cdd0

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
import Theorems.Thm_GlobalTheory_KeyPow_ClauseH_mono
import Theorems.Thm_GlobalTheory_KeyPow_KeyRule_mono
import Theorems.Thm_GlobalTheory_PowUnif_exists_chart
import Theorems.Thm_GlobalTheory_PowUnif_le_wchart_iff
import Theorems.Thm_GlobalTheory_PowUnif_val_div_g
import Theorems.Thm_GlobalTheory_PowUnif_val_g_self
import Theorems.Thm_GlobalTheory_PowUnif_val_gen
import Theorems.Thm_GlobalTheory_PowUnif_val_linComb_g

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
private theorem top_le_preimage_inf_iff {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (A B : X.Opens) :
    ⊤ ≤ x ⁻¹ᵁ (A ⊓ B) ↔ ⊤ ≤ x ⁻¹ᵁ A ∧ ⊤ ≤ x ⁻¹ᵁ B := by
  show ⊤ ≤ x ⁻¹ᵁ A ⊓ x ⁻¹ᵁ B ↔ _
  exact le_inf_iff
private theorem valAt'_units_val_ne_zero {X : Scheme.{0}} (y : Sp ℂ ⟶ X) {W : X.Opens} (hW : ⊤ ≤ y ⁻¹ᵁ W)
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
theorem _root_.solution (hL₀ : L₀.IsLB) (m : A₀.left ⟶ X) (L : LB X) (hL : L.IsLB)
    (hw : LBIso L₀ (L.pull m)) :
    ∃ a : L.ι → (Fin g → ℂ) → ℂ,
      (∀ i, DifferentiableOn ℂ (a i) (dom u m (L.U i)) ∧ ∀ z ∈ dom u m (L.U i), a i z ≠ 0) ∧
      (∀ i j, ∀ z ∈ dom u m (L.U i) ∩ dom u m (L.U j), a i z = fn u m _ (L.g i j).val z * a j z) ∧
      ∀ i (l : u.Λ) z (c : ℂ), z ∈ dom u m (L.U i) →
        (∀ b, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L₀.U b → u.fr b z = c * u.fr b (z + l)) → a i z = c * a i (z + l) := by
  obtain ⟨w, hw⟩ := hw

  have hJ : ∀ (i : L.ι) (z : Fin g → ℂ), ⊤ ≤ ((u.ex z).left ≫ m) ⁻¹ᵁ L.U i →
      ⊤ ≤ (u.ex z).left ⁻¹ᵁ (L.pull m).U (fun _ => i) := fun i z hi =>
    (PowUnif.le_wchart_iff (u.ex z).left L (fun _ : PUnit => m) (fun _ => i)).2 (fun _ => hi)

  have hM : ∀ (i j : L.ι) (z : Fin g → ℂ), ⊤ ≤ ((u.ex z).left ≫ m) ⁻¹ᵁ L.U i →
      ⊤ ≤ ((u.ex z).left ≫ m) ⁻¹ᵁ L.U j →
      valAt' (u.ex z).left ((L.pull m).U (fun _ => i) ⊓ (L.pull m).U (fun _ => j))
        ((L.pull m).g (fun _ => i) (fun _ => j)).val = fn u m (L.U i ⊓ L.U j) (L.g i j).val z := by
    intro i j z hi hj
    have h := PowUnif.val_linComb_g (u.ex z).left L (fun _ : PUnit => m) (fun _ => i) (fun _ => j)
      ((top_le_preimage_inf_iff _ _ _).2 ⟨hJ i z hi, hJ j z hj⟩)
    rw [Fintype.prod_unique] at h
    exact h

  have indep : ∀ (i : L.ι) (z : Fin g → ℂ) (b b' : L₀.ι), ⊤ ≤ ((u.ex z).left ≫ m) ⁻¹ᵁ L.U i →
      ⊤ ≤ (u.ex z).left ⁻¹ᵁ L₀.U b → ⊤ ≤ (u.ex z).left ⁻¹ᵁ L₀.U b' →
      valAt' (u.ex z).left (((L.pull m).div L₀).U ((fun _ => i), b)) (w.s ((fun _ => i), b)).val * u.fr b z =
        valAt' (u.ex z).left (((L.pull m).div L₀).U ((fun _ => i), b')) (w.s ((fun _ => i), b')).val *
          u.fr b' z := by
    intro i z b b' hi hb hb'
    have hbb : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (((L.pull m).div L₀).U ((fun _ => i), b) ⊓
        ((L.pull m).div L₀).U ((fun _ => i), b')) :=
      (top_le_preimage_inf_iff _ _ _).2 ⟨(top_le_preimage_inf_iff _ _ _).2 ⟨hJ i z hi, hb⟩, (top_le_preimage_inf_iff _ _ _).2 ⟨hJ i z hi, hb'⟩⟩
    have h1 := PowUnif.val_gen hw (u.ex z).left ((fun _ => i), b) ((fun _ => i), b') hbb
    have h2 : valAt' (u.ex z).left (((L.pull m).div L₀).U ((fun _ => i), b) ⊓
        ((L.pull m).div L₀).U ((fun _ => i), b'))
        (((L.pull m).div L₀).g ((fun _ => i), b) ((fun _ => i), b')).val =
        valAt' (u.ex z).left ((L.pull m).U (fun _ => i) ⊓ (L.pull m).U (fun _ => i))
          ((L.pull m).g (fun _ => i) (fun _ => i)).val *
        (valAt' (u.ex z).left (L₀.U b ⊓ L₀.U b') (L₀.g b b').val)⁻¹ :=
      PowUnif.val_div_g (L.pull m) L₀ (u.ex z).left (fun _ => i) (fun _ => i) b b' hbb
    have h3 : valAt' (u.ex z).left ((L.pull m).U (fun _ => i) ⊓ (L.pull m).U (fun _ => i))
        ((L.pull m).g (fun _ => i) (fun _ => i)).val = 1 := by
      rw [hM i i z hi hi]
      exact PowUnif.val_g_self hL ((u.ex z).left ≫ m) i hi
    have hbb' : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (L₀.U b ⊓ L₀.U b') := (top_le_preimage_inf_iff _ _ _).2 ⟨hb, hb'⟩
    have h4 := u.fr_compat b b' z hbb'
    have n4 := valAt'_units_val_ne_zero (u.ex z).left hbb' (L₀.g b b')
    rw [h1, h2, h3, h4]
    field_simp

  have ch : ∀ z : Fin g → ℂ, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L₀.U (Classical.choose (PowUnif.exists_chart hL₀ (u.ex z).left)) :=
    fun z => Classical.choose_spec (PowUnif.exists_chart hL₀ (u.ex z).left)
  have hdom : ∀ (i : L.ι) (z : Fin g → ℂ), z ∈ dom u m (L.U i) ↔ ⊤ ≤ ((u.ex z).left ≫ m) ⁻¹ᵁ L.U i :=
    fun _ _ => Iff.rfl
  refine ⟨fun i z => valAt' (u.ex z).left (((L.pull m).div L₀).U ((fun _ => i),
      Classical.choose (PowUnif.exists_chart hL₀ (u.ex z).left)))
      (w.s ((fun _ => i), Classical.choose (PowUnif.exists_chart hL₀ (u.ex z).left))).val *
      u.fr (Classical.choose (PowUnif.exists_chart hL₀ (u.ex z).left)) z, ?_, ?_, ?_⟩
  · intro i
    refine ⟨?_, ?_⟩
    · intro z₀ hz₀
      obtain ⟨b₀, hb₀⟩ := PowUnif.exists_chart hL₀ (u.ex z₀).left
      have hO := (u.hol (((L.pull m).div L₀).U ((fun _ => i), b₀)) (w.s ((fun _ => i), b₀)).val)
      have hz : z₀ ∈ {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (((L.pull m).div L₀).U ((fun _ => i), b₀))} :=
        (top_le_preimage_inf_iff _ _ _).2 ⟨hJ i z₀ hz₀, hb₀⟩
      have hsub : {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (((L.pull m).div L₀).U ((fun _ => i), b₀))} ⊆
          {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L₀.U b₀} := fun z hz => ((top_le_preimage_inf_iff _ _ _).1 hz).2
      have hd : DifferentiableAt ℂ (fun z => valAt' (u.ex z).left (((L.pull m).div L₀).U ((fun _ => i), b₀))
          (w.s ((fun _ => i), b₀)).val * u.fr b₀ z) z₀ :=
        (hO.2.mul ((u.fr_hol b₀).mono hsub)).differentiableAt (hO.1.mem_nhds hz)
      refine (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
      filter_upwards [hO.1.mem_nhds hz] with z hz'
      have hz1 := (top_le_preimage_inf_iff _ _ _).1 hz'
      have hi : ⊤ ≤ ((u.ex z).left ≫ m) ⁻¹ᵁ L.U i :=
        (PowUnif.le_wchart_iff (u.ex z).left L (fun _ : PUnit => m) (fun _ => i)).1 hz1.1 PUnit.unit
      exact indep i z _ _ hi (ch z) hz1.2
    · intro z hz
      have hzz : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (((L.pull m).div L₀).U ((fun _ => i),
          Classical.choose (PowUnif.exists_chart hL₀ (u.ex z).left))) :=
        (top_le_preimage_inf_iff _ _ _).2 ⟨hJ i z hz, ch z⟩
      exact mul_ne_zero (valAt'_units_val_ne_zero _ hzz _) (u.fr_ne _ z (ch z))
  · intro i j z hz
    dsimp only
    obtain ⟨hzi, hzj⟩ := hz
    have hzi' : ⊤ ≤ ((u.ex z).left ≫ m) ⁻¹ᵁ L.U i := hzi
    have hzj' : ⊤ ≤ ((u.ex z).left ≫ m) ⁻¹ᵁ L.U j := hzj
    set b := Classical.choose (PowUnif.exists_chart hL₀ (u.ex z).left) with hbdef
    have hbb : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (((L.pull m).div L₀).U ((fun _ => i), b) ⊓
        ((L.pull m).div L₀).U ((fun _ => j), b)) :=
      (top_le_preimage_inf_iff _ _ _).2 ⟨(top_le_preimage_inf_iff _ _ _).2 ⟨hJ i z hzi', ch z⟩, (top_le_preimage_inf_iff _ _ _).2 ⟨hJ j z hzj', ch z⟩⟩
    have h1 := PowUnif.val_gen hw (u.ex z).left ((fun _ => i), b) ((fun _ => j), b) hbb
    have h2 : valAt' (u.ex z).left (((L.pull m).div L₀).U ((fun _ => i), b) ⊓
        ((L.pull m).div L₀).U ((fun _ => j), b))
        (((L.pull m).div L₀).g ((fun _ => i), b) ((fun _ => j), b)).val =
        valAt' (u.ex z).left ((L.pull m).U (fun _ => i) ⊓ (L.pull m).U (fun _ => j))
          ((L.pull m).g (fun _ => i) (fun _ => j)).val *
        (valAt' (u.ex z).left (L₀.U b ⊓ L₀.U b) (L₀.g b b).val)⁻¹ :=
      PowUnif.val_div_g (L.pull m) L₀ (u.ex z).left (fun _ => i) (fun _ => j) b b hbb
    rw [h1, h2, hM i j z hzi' hzj', PowUnif.val_g_self hL₀ (u.ex z).left b (ch z), inv_one, _root_.mul_one]
    ring
  · intro i l z c hz hper
    have hx : (u.ex (z + l)).left = (u.ex z).left := by rw [ex_add_lattice]
    have hz' : ⊤ ≤ ((u.ex z).left ≫ m) ⁻¹ᵁ L.U i := hz
    have hzl : ⊤ ≤ ((u.ex (z + l)).left ≫ m) ⁻¹ᵁ L.U i := by rw [hx]; exact hz'
    have e1 := indep i (z + l) (Classical.choose (PowUnif.exists_chart hL₀ (u.ex (z + l)).left))
      (Classical.choose (PowUnif.exists_chart hL₀ (u.ex z).left)) hzl (ch (z + l)) (by rw [hx]; exact ch z)
    dsimp only
    rw [e1, hper _ (ch z), hx]
    ring
end GlobalTheory.KS
