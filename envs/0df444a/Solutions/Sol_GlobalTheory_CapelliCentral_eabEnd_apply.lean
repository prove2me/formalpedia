-- Prove2me | solution 1 for GlobalTheory.CapelliCentral.eabEnd_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:37:25.241787+00:00
-- url     : https://prove2.me/submissions/fb08ce42-4def-4a18-8421-bf6d16776885

import Mathlib
import Definitions.Def_Formalism_FormalDegreeBessel_StatementIO
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_QuotientSettingHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SmoothAddSmul
import Theorems.Thm_Formalism_REAL_complex_parts_mem_lie_algebra_holds
import Theorems.Thm_Formalism_REAL_f1alg_exp_inUJ
import Theorems.Thm_Formalism_REAL_lie_algebra_real_smul_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix
open scoped ContDiff
noncomputable section
namespace GlobalTheory.CapelliCentral
open Formalism.REAL Formalism.QuantumDeterminants
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {ε : Fin n → Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
open Matrix in
open scoped ContDiff in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
variable {n : ℕ} {ε : Fin n → Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] in
private theorem inUJ_mul_foundation {g k : Matrix (Fin n) (Fin n) ℂ}
    (hg : _root_.Formalism.REAL.inUJ ε g) (hk : _root_.Formalism.REAL.inUJ ε k) : _root_.Formalism.REAL.inUJ ε (g * k) := by
  unfold _root_.Formalism.REAL.inUJ at *
  rw [conjTranspose_mul,
    show kᴴ * gᴴ * _root_.Formalism.REAL.Jm ε * (g * k) = kᴴ * (gᴴ * _root_.Formalism.REAL.Jm ε * g) * k by
      simp only [Matrix.mul_assoc], hg, hk]
open Matrix in
open scoped ContDiff in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
variable {n : ℕ} {ε : Fin n → Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] in
private theorem rdV_congr_of_eqOn_inUJ {X : Matrix (Fin n) (Fin n) ℂ} (hX : _root_.Formalism.REAL.inG ε X)
    {f f' : Matrix (Fin n) (Fin n) ℂ → E} (h : ∀ g, _root_.Formalism.REAL.inUJ ε g → f g = f' g)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : _root_.Formalism.REAL.inUJ ε g) : _root_.Formalism.REAL.RdV X f g = _root_.Formalism.REAL.RdV X f' g := by
  unfold _root_.Formalism.REAL.RdV
  congr 1
  funext t
  exact h _ (inUJ_mul_foundation hg (_root_.Formalism.REAL.f1alg_exp_inUJ ε _ (_root_.Formalism.REAL.lie_algebra_real_smul_mem ε hX t)))
end GlobalTheory.CapelliCentral
namespace GlobalTheory
open Formalism.REAL Formalism.QuantumDeterminants CapelliCentral
end GlobalTheory
end
end

set_option autoImplicit false
open Matrix
open scoped ContDiff
noncomputable section
open GlobalTheory GlobalTheory.CapelliCentral
open Formalism.REAL Formalism.QuantumDeterminants
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {ε : Fin n → Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
open Matrix
open scoped ContDiff
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {ε : Fin n → Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace GlobalTheory.CapelliCentral
namespace _root_.GlobalTheory.CapelliCentral
theorem _root_.solution (a b : Fin n) (F : _root_.GlobalTheory.CapelliCentral.smoothSpace ε E)
    {f : Matrix (Fin n) (Fin n) ℂ → E} (h : ∀ g, _root_.Formalism.REAL.inUJ ε g → F.1 g = f g)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : _root_.Formalism.REAL.inUJ ε g) :
    (_root_.GlobalTheory.CapelliCentral.eabEnd ε E a b F).1 g = _root_.Formalism.REAL.EabV ε a b f g := by
  obtain ⟨hP, hQ, -, -⟩ := _root_.Formalism.REAL.complex_parts_mem_lie_algebra_holds n ε (Matrix.single a b 1)
  show _root_.GlobalTheory.CapelliCentral.cut ε (_root_.Formalism.REAL.EabV ε a b F.1) g = _
  rw [_root_.GlobalTheory.CapelliCentral.cut_of_mem _ hg]
  show _root_.Formalism.REAL.EcV ε _ _ g = _root_.Formalism.REAL.EcV ε _ _ g
  unfold _root_.Formalism.REAL.EcV
  rw [rdV_congr_of_eqOn_inUJ hP h hg, rdV_congr_of_eqOn_inUJ hQ h hg]
end _root_.GlobalTheory.CapelliCentral
end GlobalTheory.CapelliCentral
