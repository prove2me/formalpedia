-- Prove2me | solution 1 for GlobalTheory.ckOn_inCC_congr_on_group
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:21:56.250139+00:00
-- url     : https://prove2.me/submissions/f5b708d0-500f-4f04-b0c8-55d6bbe369f3

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_LetterProductDoubleDegreeCount
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CkOnInCCCongrOnGroup
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_In_key
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_key
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_trans

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset
namespace GlobalTheory
private theorem exp_real_smul_mem_UJset_of_inG {n : ℕ} (H X : Matrix (Fin n) (Fin n) ℂ) (hX : X.conjTranspose * H + H * X = 0)
    (t : ℝ) : (NormedSpace.exp ((t : ℂ) • X)).conjTranspose * H * NormedSpace.exp ((t : ℂ) • X) = H := by
  set Y : Matrix (Fin n) (Fin n) ℂ := (t : ℂ) • X with hYdef
  have hHX : H * X = -(X.conjTranspose * H) := eq_neg_of_add_eq_zero_right hX
  have hY : SemiconjBy H Y (-Y.conjTranspose) := by
    show H * Y = -Y.conjTranspose * H
    rw [hYdef, Matrix.mul_smul, hHX, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
      Matrix.neg_mul, Matrix.smul_mul, smul_neg]
  have key : NormedSpace.exp (-(-Y.conjTranspose)) * H * NormedSpace.exp Y = H := by
    letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
    letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
    letI : NormedSpace ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedSpace
    letI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℂ _
    exact hY.exp_neg_mul_mul_exp_eq_self
  rwa [neg_neg, Matrix.exp_conjTranspose] at key
private theorem mul_mem_UH_Hpk' {k r : ℕ} {g h : B.Mat k r} (hg : g ∈ B.GV k r) (hh : h ∈ B.GV k r) :
    g * h ∈ B.GV k r := by
  have hg' : g.conjTranspose * Hpk k r * g = Hpk k r := hg
  have hh' : h.conjTranspose * Hpk k r * h = Hpk k r := hh
  show (g * h).conjTranspose * Hpk k r * (g * h) = Hpk k r
  rw [Matrix.conjTranspose_mul, show h.conjTranspose * g.conjTranspose * Hpk k r * (g * h) = h.conjTranspose * (g.conjTranspose * Hpk k r * g) * h by
    simp only [Matrix.mul_assoc], hg', hh']
private theorem exp_smul_mem_UJset' {k r : ℕ} {X : B.Mat k r} (hX : B.inLie k r X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ B.GV k r :=
  exp_real_smul_mem_UJset_of_inG (Hpk k r) X hX t
private theorem rdV_congr_on_GV {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {X : B.Mat k r} (hX : B.inLie k r X) {f f' : B.Mat k r → E}
    (h : ∀ g ∈ B.GV k r, f g = f' g) : ∀ g ∈ B.GV k r, RdV X f g = RdV X f' g := by
  intro g hg
  simp only [RdV]
  congr 1
  funext t
  exact h _ (mul_mem_UH_Hpk' hg (exp_smul_mem_UJset' hX t))
private theorem ldV_congr_on_GV {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {X : B.Mat k r} (hX : B.inLie k r X) {f f' : B.Mat k r → E}
    (h : ∀ g ∈ B.GV k r, f g = f' g) : ∀ g ∈ B.GV k r, B.LdV X f g = B.LdV X f' g := by
  intro g hg
  simp only [B.LdV]
  congr 1
  funext t
  have hneg : -((t : ℂ) • X) = ((-t : ℝ) : ℂ) • X := by rw [Complex.ofReal_neg, neg_smul]
  rw [hneg]
  exact h _ (mul_mem_UH_Hpk' (exp_smul_mem_UJset' hX (-t)) hg)
private theorem rw_congr_on_GV {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (v : List (B.Mat k r)) (hv : ∀ X ∈ v, B.inLie k r X) {f f' : B.Mat k r → E}
    (h : ∀ g ∈ B.GV k r, f g = f' g) : ∀ g ∈ B.GV k r, B.Rw v f g = B.Rw v f' g := by
  induction v with
  | nil => exact h
  | cons X v ih =>
    exact rdV_congr_on_GV (hv X List.mem_cons_self) (ih fun Y hY => hv Y (List.mem_cons_of_mem X hY))
private theorem dLR_congr_on_GV {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (u v : List (B.Mat k r)) (hu : ∀ X ∈ u, B.inLie k r X) (hv : ∀ X ∈ v, B.inLie k r X)
    {f f' : B.Mat k r → E} (h : ∀ g ∈ B.GV k r, f g = f' g) :
    ∀ g ∈ B.GV k r, B.dLR u v f g = B.dLR u v f' g := by
  induction u with
  | nil => exact rw_congr_on_GV v hv h
  | cons X u ih =>
    exact ldV_congr_on_GV (hu X List.mem_cons_self) (ih fun Y hY => hu Y (List.mem_cons_of_mem X hY))
end GlobalTheory
end

set_option autoImplicit false
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (A : ℝ) (F F' : B.Mat k r → E), (∀ g ∈ B.GV k r, F g = F' g) → (B.CkOn ⊤ (B.GV k r) F → B.CkOn ⊤ (B.GV k r) F') ∧ ∀ m : ℕ, B.InCC A m F → B.InCC A m F' := by
  intro k r E _ _ A F F' h
  have hck : ∀ m : ℕ∞, B.CkOn m (B.GV k r) F → B.CkOn m (B.GV k r) F' := by
    intro m hF g₀ hg₀
    obtain ⟨U, f', hU, hg₀U, hf', hfU⟩ := hF g₀ hg₀
    exact ⟨U, f', hU, hg₀U, hf', fun g hgU hgG => (h g hgG).symm.trans (hfU g hgU hgG)⟩
  refine ⟨hck ⊤, fun m hF => ?_⟩
  unfold B.InCC B.CCle at hF ⊢
  obtain ⟨c, hc1, hc2⟩ := hF
  refine ⟨c, hck _ hc1, fun u v hu hv hlen g hg => ?_⟩
  rw [← dLR_congr_on_GV u v (fun X hX => (hu X hX).1) (fun X hX => (hv X hX).1) h g hg]
  exact hc2 u v hu hv hlen g hg
end GlobalTheory
