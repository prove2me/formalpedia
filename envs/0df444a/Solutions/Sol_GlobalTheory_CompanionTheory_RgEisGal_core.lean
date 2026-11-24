-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisGal.core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:57:23.157542+00:00
-- url     : https://prove2.me/submissions/53c002b3-3c5d-46f5-8b3e-435b387837eb

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DifferentiableAffLine
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ChamberPairThreeFour
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_mem_Om1
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_mem_Om2
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_mem_Om3
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_mem_Om4
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_oc_coneI
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_isOpen_convex_Om1
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_isOpen_convex_Om2
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_isOpen_convex_Om3
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_isOpen_convex_Om4
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_isOpen_chamberPairOneTwo
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_isOpen_V12
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_isOpen_V23
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_isOpen_V34
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_nonempty_V01
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_nonempty_V12
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_nonempty_V23
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_nonempty_V34
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_exists_midpoint
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_chain4
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_Fac_left_fst
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_Fac_left_snd
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_Fac_strip_snd
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_lineHol_exp
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_Fac_comp
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_Fac_left
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_Fac_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_Fac_strip
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_TubeGood_chg
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_TubeGood_comp
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_TubeGood_mono
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_TubeGood_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisGal
variable {T : Type} [TopologicalSpace T] [FirstCountableTopology T]
  {ES EA EB W : Type} [NormedAddCommGroup ES] [NormedSpace ℂ ES] [NormedAddCommGroup EA]
  [NormedSpace ℂ EA] [NormedAddCommGroup EB] [NormedSpace ℂ EB] [NormedAddCommGroup W]
  [NormedSpace ℂ W] [CompleteSpace W]
namespace GlobalTheory.CompanionTheory.RgEisGal
theorem _root_.solution (hId : IdTube) (hTC : TubeChain) (N R : ℝ) (hR : |N| + 1 ≤ R)
    {o₀ : ℂ × ℂ → T → ES →L[ℂ] W} {oc oa : ℂ × ℂ → T → EB →L[ℂ] W} {ob ol : ℂ × ℂ → T → EA →L[ℂ] W}
    (g₀ : TubeGood o₀ (coneI (10 * R))) (gc : TubeGood oc (coneC (10 * R)))
    (ga : TubeGood oa (coneA (10 * R))) (gb : TubeGood ob (coneC (10 * R)))
    (gl : TubeGood ol (coneI (10 * R)))
    {Dc Da Db d : ℂ → ℂ} (hDc : StripEntire Dc) (hDa : StripEntire Da) (hDb : StripEntire Db)
    (hd : StripEntire d)
    {Op₀ O : ℂ → ES →L[ℂ] EB} {Opc : ℂ → EB →L[ℂ] EB} {Opa : ℂ → EB →L[ℂ] EA} {Opb : ℂ → EA →L[ℂ] EA}
    (hOp₀ : LeftGood Op₀ (-R)) (hO : LeftGood O (1 / 2)) (hOpc : LeftGood Opc (-R))
    (hOpa : LeftGood Opa (-R)) (hOpb : LeftGood Opb (-R))
    (J₀ : ∀ l ∈ tube (chamberPairOneTwo (100 * R)), ∀ g, Dc (yv N l) • o₀ l g = (oc (mc N l) g).comp (Op₀ l.1))
    (J₁ : ∀ l ∈ tube (chamberPairTwoThree (100 * R)), ∀ g,
      Da (zv N l) • oc (mc N l) g = (oa (ma N l) g).comp (Opc (yv N l)))
    (J₂ : ∀ l ∈ tube (chamberPairThreeFour (100 * R)), ∀ g,
      Db l.2 • oa (ma N l) g = (ob (mb N l) g).comp (Opa (zv N l)))
    (J₃ : ∀ l ∈ tube (chamberPairFourLast (100 * R)), ∀ g,
      (-d (nz N l)) • (ob (mb N l) g).comp ((Opa (zv N l)).comp ((Opc (yv N l)).comp (Op₀ l.1))) =
        (ol (ml N l) g).comp ((Opb l.2).comp ((Opa (zv N l)).comp ((Opc (yv N l)).comp (O l.1))))) :
    ∃ Φ : ℂ × ℂ → T → ES →L[ℂ] W, TubeGood Φ Set.univ ∧
      (∀ l ∈ tube (coneI (10 * R)), ∀ g, Φ l g = Complex.exp (l.1 ^ 2 + l.2 ^ 2) •
        (Dc (yv N l) * Da (zv N l) * Db l.2) • o₀ l g) ∧
      ∀ l ∈ tube (Om4 N (10 * R)), ∀ g, (-d (nz N l)) • Φ l g = Complex.exp (l.1 ^ 2 + l.2 ^ 2) •
        (ol (ml N l) g).comp ((Opb l.2).comp ((Opa (zv N l)).comp ((Opc (yv N l)).comp (O l.1)))) := by
  have hN := abs_le.1 (show |N| ≤ R - 1 by linarith)
  have hN₁ := hN.1
  have hN₂ := hN.2
  have hR1 : 1 ≤ R := by linarith [abs_nonneg N]

  set F₀ : ℂ × ℂ → T → ES →L[ℂ] W := fun l g => (Dc (yv N l) * Da (zv N l) * Db l.2) • o₀ l g with hF₀
  set F₁ : ℂ × ℂ → T → ES →L[ℂ] W :=
    fun l g => (Da (zv N l) * Db l.2) • (oc (mc N l) g).comp (Op₀ l.1) with hF₁
  set F₂ : ℂ × ℂ → T → ES →L[ℂ] W :=
    fun l g => Db l.2 • (oa (ma N l) g).comp ((Opc (yv N l)).comp (Op₀ l.1)) with hF₂
  set F₃ : ℂ × ℂ → T → ES →L[ℂ] W :=
    fun l g => (ob (mb N l) g).comp ((Opa (zv N l)).comp ((Opc (yv N l)).comp (Op₀ l.1))) with hF₃
  have t₀ : TubeGood F₀ (coneI (10 * R)) :=
    TubeGood_smul (Fac_mul (Fac_mul (Fac_strip hDc _ _ _ _) (Fac_strip hDa _ _ _ _))
      (Fac_strip_snd hDb _)) g₀
  have t₁ : TubeGood F₁ (Om1 N (10 * R)) :=
    TubeGood_smul (Fac_mul (Fac_strip hDa _ _ _ _) (Fac_strip_snd hDb _))
      (TubeGood_comp (TubeGood_chg gc _ _ _ _ _ _)
        (Fac_left_fst hOp₀ fun x hx => by have := (mem_Om1.1 hx).1; linarith))
  have t₂ : TubeGood F₂ (Om2 N (10 * R)) :=
    TubeGood_smul (Fac_strip_snd hDb _)
      (TubeGood_comp (TubeGood_chg ga _ _ _ _ _ _)
        (Fac_comp
          (Fac_left hOpc _ _ _ fun x hx => by
            have := (mem_Om2.1 hx).1
            simp only [affR]; linarith)
          (Fac_left_fst hOp₀ fun x hx => by
            have := mem_Om2.1 hx
            linarith [this.1, this.2])))
  have t₃ : TubeGood F₃ (Om3 N (10 * R)) :=
    TubeGood_comp (TubeGood_chg gb _ _ _ _ _ _)
      (Fac_comp
        (Fac_left hOpa _ _ _ fun x hx => by
          have := (mem_Om3.1 hx).1
          simp only [affR]; linarith)
        (Fac_comp
          (Fac_left hOpc _ _ _ fun x hx => by
            have := mem_Om3.1 hx
            simp only [affR]; linarith [this.1, this.2])
          (Fac_left_fst hOp₀ fun x hx => by
            have := (mem_Om3.1 hx).2
            linarith)))
  have j₀ : ∃ V : Set (ℝ × ℝ), IsOpen V ∧ V.Nonempty ∧ V ⊆ coneI (10 * R) ∩ Om1 N (10 * R) ∧
      ∀ l ∈ tube V, ∀ g, F₀ l g = F₁ l g := by
    refine ⟨chamberPairOneTwo (100 * R), isOpen_chamberPairOneTwo _, nonempty_V01 _, ?_, ?_⟩
    · rintro x ⟨h₁, h₂⟩
      refine ⟨?_, mem_Om1.2 ⟨?_, ?_⟩⟩
      · simp only [coneI, Set.mem_setOf_eq]
        constructor <;> linarith
      all_goals linarith
    · intro l hl g
      change (Dc (yv N l) * Da (zv N l) * Db l.2) • o₀ l g =
        (Da (zv N l) * Db l.2) • (oc (mc N l) g).comp (Op₀ l.1)
      rw [← J₀ l hl g, smul_smul]
      congr 1
      ring
  have j₁ : ∃ V : Set (ℝ × ℝ), IsOpen V ∧ V.Nonempty ∧ V ⊆ Om1 N (10 * R) ∩ Om2 N (10 * R) ∧
      ∀ l ∈ tube V, ∀ g, F₁ l g = F₂ l g := by
    refine ⟨chamberPairTwoThree (100 * R), isOpen_V12 _, nonempty_V12 _, ?_, ?_⟩
    · rintro x ⟨h₁, h₂⟩
      refine ⟨mem_Om1.2 ⟨?_, ?_⟩, mem_Om2.2 ⟨?_, ?_⟩⟩ <;> linarith
    · intro l hl g
      change (Da (zv N l) * Db l.2) • (oc (mc N l) g).comp (Op₀ l.1) =
        Db l.2 • (oa (ma N l) g).comp ((Opc (yv N l)).comp (Op₀ l.1))
      rw [← ContinuousLinearMap.comp_assoc _ (Opc (yv N l)), ← J₁ l hl g,
        ContinuousLinearMap.smul_comp, smul_smul]
      congr 1
      ring
  have j₂ : ∃ V : Set (ℝ × ℝ), IsOpen V ∧ V.Nonempty ∧ V ⊆ Om2 N (10 * R) ∩ Om3 N (10 * R) ∧
      ∀ l ∈ tube V, ∀ g, F₂ l g = F₃ l g := by
    refine ⟨chamberPairThreeFour (100 * R), isOpen_V23 _, nonempty_V23 _, ?_, ?_⟩
    · rintro x ⟨h₁, h₂⟩
      refine ⟨mem_Om2.2 ⟨?_, ?_⟩, mem_Om3.2 ⟨?_, ?_⟩⟩ <;> linarith
    · intro l hl g
      change Db l.2 • (oa (ma N l) g).comp ((Opc (yv N l)).comp (Op₀ l.1)) =
        (ob (mb N l) g).comp ((Opa (zv N l)).comp ((Opc (yv N l)).comp (Op₀ l.1)))
      rw [← ContinuousLinearMap.comp_assoc _ (Opa (zv N l)), ← J₂ l hl g,
        ContinuousLinearMap.smul_comp]
  obtain ⟨Φ, hΦ, e₀, e₃⟩ := chain4 hTC (F₀ := F₀) (F₁ := F₁) (F₂ := F₂) (F₃ := F₃)
    ⟨(oc_coneI _).1, (oc_coneI _).2, t₀⟩ ⟨(isOpen_convex_Om1 N _).1, (isOpen_convex_Om1 N _).2, t₁⟩
    ⟨(isOpen_convex_Om2 N _).1, (isOpen_convex_Om2 N _).2, t₂⟩ ⟨(isOpen_convex_Om3 N _).1, (isOpen_convex_Om3 N _).2, t₃⟩
    j₀ j₁ j₂ (exists_midpoint N _)
  refine ⟨Φ, hΦ, e₀, fun l hl g => ?_⟩

  have hsub : chamberPairFourLast (100 * R) ⊆ Om4 N (10 * R) ∩ Om3 N (10 * R) := by
    rintro x ⟨h₁, h₂⟩
    refine ⟨mem_Om4.2 ⟨⟨?_, ?_⟩, ?_⟩, mem_Om3.2 ⟨?_, ?_⟩⟩ <;> linarith
  have hneg : StripEntire fun z => -d z :=
    ⟨hd.1.neg, fun b c => by
      obtain ⟨M, hM⟩ := hd.2 b c
      exact ⟨M, fun z h₁ h₂ => by simpa using hM z h₁ h₂⟩⟩
  have hleft : LineHol (fun l : ℂ × ℂ => (-d (nz N l)) • Φ l g) (tube (Om4 N (10 * R))) :=
    (TubeGood_smul (Fac_strip hneg (-1) 0 N _) (TubeGood_mono hΦ (Set.subset_univ _))).hol g
  have hcomp : TubeGood (fun (l : ℂ × ℂ) g => (ol (ml N l) g).comp
      ((Opb l.2).comp ((Opa (zv N l)).comp ((Opc (yv N l)).comp (O l.1))))) (Om4 N (10 * R)) :=
    TubeGood_comp (TubeGood_mono (TubeGood_chg gl _ _ _ _ _ _) fun x hx => hx.1)
      (Fac_comp
        (Fac_left_snd hOpb fun x hx => by
          have := (mem_Om4.1 hx).1.1
          linarith)
        (Fac_comp
          (Fac_left hOpa _ _ _ fun x hx => by
            have := mem_Om4.1 hx
            simp only [affR]; linarith [this.1.1, this.2])
          (Fac_comp
            (Fac_left hOpc _ _ _ fun x hx => by
              have := mem_Om4.1 hx
              simp only [affR]; linarith [this.1.1, this.2])
            (Fac_left_fst hO fun x hx => (mem_Om4.1 hx).2))))
  have hright : LineHol (fun l : ℂ × ℂ => Complex.exp (l.1 ^ 2 + l.2 ^ 2) •
      (ol (ml N l) g).comp ((Opb l.2).comp ((Opa (zv N l)).comp ((Opc (yv N l)).comp (O l.1)))))
      (tube (Om4 N (10 * R))) :=
    fun p v => (lineHol_exp _ p v).smul (hcomp.hol g p v)
  refine hId (ES →L[ℂ] W) (Om4 N (10 * R)) (chamberPairFourLast (100 * R)) _ _ (isOpen_convex_Om4 N _).1 (isOpen_convex_Om4 N _).2
    (isOpen_V34 _) (nonempty_V34 _) (fun x hx => (hsub hx).1) hleft hright ?_ hl
  intro l' hl'
  have e := e₃ l' (show (l'.1.re, l'.2.re) ∈ Om3 N (10 * R) from (hsub hl').2) g
  simp only [e]
  rw [smul_comm]
  exact congrArg _ (J₃ l' hl' g)
end GlobalTheory.CompanionTheory.RgEisGal
