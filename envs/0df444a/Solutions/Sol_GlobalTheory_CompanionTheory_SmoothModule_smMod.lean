-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SmoothModule.smMod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:19:23.175908+00:00
-- url     : https://prove2.me/submissions/c90bb473-1053-4e00-ab25-2d02a6a04718

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_GlRelOfBracket
import Theorems.Thm_GlobalTheory_CompanionTheory_SmoothModule_theta_single
import Theorems.Thm_GlobalTheory_CompanionTheory_SmoothModule_inG_comm
import Theorems.Thm_GlobalTheory_CompanionTheory_SmoothModule_inG_conj
import Theorems.Thm_GlobalTheory_CompanionTheory_SmoothModule_conj_single
import Theorems.Thm_GlobalTheory_CompanionTheory_SmoothModule_cext_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_SmoothModule_cext_of_inG
import Theorems.Thm_GlobalTheory_CompanionTheory_SmoothModule_bracket_ext
import Theorems.Thm_GlobalTheory_CompanionTheory_SmoothModule_glRel_of_bracket
import Theorems.Thm_GlobalTheory_CompanionTheory_SmoothModule_adj_ext
import Theorems.Thm_GlobalTheory_CompanionTheory_SmoothModule_skew
import Theorems.Thm_GlobalTheory_CompanionTheory_SmoothModule_conj_deriv
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply



set_option autoImplicit false
open Matrix Finset
open scoped InnerProductSpace
open PI.UpqRep (IsURepOn UJset inG)
open PI.DSInfCharCap (dsigC thetaJ)
open PI.PhMeasCore (dsig smoothVecs)
open Formalism.REAL (Jm)
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SmoothModule
variable {n : ℕ} {ε : Fin n → Bool}
namespace GlobalTheory.CompanionTheory.SmoothModule
theorem _root_.solution (hL : CompanionTheory.D.DSIC.SmLin) (hB : CompanionTheory.D.DSIC.SmBracket) : CompanionTheory.D.DSIC.SmMod := by
  classical
  intro n ε H _ _ σ hσ
  obtain ⟨h0, hadd, hsm, hst, hd, hlin⟩ := hL n ε H σ hσ
  have hbr := hB n ε H σ hσ
  let S : Submodule ℂ H :=
    { carrier := smoothVecs (Jm ε) σ
      add_mem' := fun {a b} ha hb => hadd a ha b hb
      zero_mem' := h0
      smul_mem' := fun c {x} hx => hsm c x hx }
  let D : ∀ X, inG ε X → Module.End ℂ S := fun X hX =>
    { toFun := fun v => ⟨dsig σ X v, (hd X hX v v.2).1⟩
      map_add' := fun v w => Subtype.ext <| by
        have h1 := (hd X hX _ (v + w).2).2
        simp only [Submodule.coe_add, map_add] at h1
        exact h1.unique ((hd X hX v v.2).2.add (hd X hX w w.2).2)
      map_smul' := fun c v => Subtype.ext <| by
        have h1 := (hd X hX _ (c • v).2).2
        simp only [Submodule.coe_smul, map_smul] at h1
        exact h1.unique ((hd X hX v v.2).2.const_smul c) }
  let d : Matrix (Fin n) (Fin n) ℂ → Module.End ℂ S := fun X => if hX : inG ε X then D X hX else 0
  have hdv : ∀ X, inG ε X → ∀ v : S, (d X v : H) = dsig σ X v := by
    intro X hX v
    simp only [d, dif_pos hX]
    rfl
  have dadd : ∀ X Y, inG ε X → inG ε Y → d (X + Y) = d X + d Y := by
    intro X Y hX hY
    ext v
    rw [LinearMap.add_apply, Submodule.coe_add, hdv _ (inG_add hX hY), hdv _ hX, hdv _ hY]
    exact (hlin X Y hX hY v v.2).1
  have dsmul : ∀ (s : ℝ) X, inG ε X → d ((s : ℂ) • X) = (s : ℂ) • d X := by
    intro s X hX
    ext v
    rw [LinearMap.smul_apply, Submodule.coe_smul, hdv _ (inG_smul s hX), hdv _ hX]
    exact (hlin X X hX hX v v.2).2 s
  obtain ⟨C, hC, hCX⟩ : ∃ C : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ S,
      (∀ Y (v : S), (C Y v : H) = dsigC ε σ Y v) ∧ ∀ X, inG ε X → ∀ v : S, (C X v : H) = dsig σ X v := by
    refine ⟨cext ε d dadd dsmul, fun Y v => ?_, fun X hX v => ?_⟩
    · rw [cext_apply, LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_add, Submodule.coe_smul,
        hdv _ (inG_re Y), hdv _ (inG_im Y)]
      rfl
    · rw [cext_of_inG _ _ _ hX, hdv _ hX]
  have hder : ∀ X, inG ε X → ∀ v : S,
      HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v) (C X v : H) 0 := by
    intro X hX v
    rw [hCX X hX]
    exact (hd X hX v v.2).2
  refine ⟨S, fun a b => C (single a b 1), fun v => Iff.rfl, fun a b v => hC _ v, fun X hX v => ?_, ?_, ?_,
    hst, ?_⟩
  · have h : X = ∑ a, ∑ b, X a b • single a b (1 : ℂ) := by
      simp only [smul_single, smul_eq_mul, mul_one]
      exact matrix_eq_sum_single X
    have h2 : (C X v : H) = ∑ a, ∑ b, X a b • (C (single a b 1) v : H) := by
      conv_lhs => rw [h]
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum,
        Submodule.coe_smul]
    rw [← h2]
    exact hder X hX v
  · refine glRel_of_bracket C (bracket_ext (ε := ε) C fun X Y hX hY => ?_)
    ext v
    simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, hCX _ hX, hCX _ hY,
      hCX _ (inG_comm hX hY)]
    exact hbr X Y hX hY v v.2
  · intro a b x y
    rw [adj_ext (ε := ε) C (fun X hX x y => skew hσ hX (hder X hX x) (hder X hX y)), theta_single]
    simp only [map_smul, LinearMap.smul_apply, inner_smul_right]
    ring
  · intro g hg a b v w hw
    have h1 : ∀ X, inG ε X → σ g (C X v) = C (g * X * g⁻¹) w := by
      intro X hX
      have h := hder _ (inG_conj hg hX) w
      rw [hw] at h
      exact (conj_deriv hσ hX hg (hder X hX v)).unique h
    have h2 : ∀ Y, σ g (C Y v) = C (g * Y * g⁻¹) w := by
      intro Y
      rw [← re_add_im (ε := ε) Y]
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, map_add, map_smul,
        LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_add, Submodule.coe_smul,
        h1 _ (inG_re Y), h1 _ (inG_im Y)]
    rw [h2, conj_single]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum,
      Submodule.coe_smul]
end GlobalTheory.CompanionTheory.SmoothModule
