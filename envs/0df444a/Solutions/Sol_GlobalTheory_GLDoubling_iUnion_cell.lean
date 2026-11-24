-- Prove2me | solution 1 for GlobalTheory.GLDoubling.iUnion_cell
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:22:50.084808+00:00
-- url     : https://prove2.me/submissions/2732555b-4040-4752-baa2-b8d8a2e8d7fe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Cartan
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Theorems.Thm_GlobalTheory_GLDoubling_val_torusElt
import Theorems.Thm_Formalism_UG_P_cartan_decomp_gen
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_SmGL_ord_eq_one
import Theorems.Thm_GlobalTheory_SmGL_ord_eq_zero_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Doubling.flatSec_self
attribute [local simp] GlobalTheory.Doubling.val_aOf
attribute [local simp] GlobalTheory.Doubling.val_leviOf



set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling Formalism.UG
open scoped NNReal Pointwise
open GlobalTheory GlobalTheory.GLDoubling
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (n : Type) [Fintype n] [DecidableEq n]
variable {k n}
namespace GlobalTheory.GLDoubling
theorem _root_.solution {N : ℕ} {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) :
    ⋃ e : {e : Fin N → ℤ // Antitone e}, cell k (Fin N) ϖ e = Set.univ := by
  refine Set.eq_univ_of_forall fun g => ?_
  obtain ⟨c, hc0, hc⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors 𝒪[k])
    (fun ij : Fin N × Fin N => g.1 ij.1 ij.2) |>.imp
      (fun c hc => And.intro (nonZeroDivisors.coe_ne_zero c) hc)
  choose G hG using hc
  obtain ⟨a, ha, k₁, h₁, k₂, h₂, e⟩ :=
    Formalism.UG.P.cartan_decomp_gen 𝒪[k] (valuation k) (fun _ => Iff.rfl) (ϖ : k) ϖ.ne_zero
      (fun x hx => ⟨ord k (Units.mk0 x hx), by
        have h1 : ∀ m : ℤ, ord k (ϖ ^ m) = m := fun m => by
          let o : kˣ →* Multiplicative ℤ := MonoidHom.mk' (fun x => .ofAdd (ord k x)) fun x y => by
            rw [ord_mul, ofAdd_add]
          have := map_zpow o ϖ m
          rw [show o ϖ = .ofAdd 1 from congrArg Multiplicative.ofAdd (ord_eq_one hϖ), ← ofAdd_zsmul,
            smul_eq_mul, mul_one] at this
          exact this
        have h2 := ord_eq_zero_iff.1 (show ord k (Units.mk0 x hx * ϖ ^ (-ord k (Units.mk0 x hx))) = 0 by
          rw [ord_mul, h1, add_neg_cancel])
        rw [Units.val_mul, map_mul, Units.val_zpow_eq_zpow_val, map_zpow₀, _root_.zpow_neg,
          mul_inv_eq_one₀ (zpow_ne_zero _ (by simp))] at h2
        exact h2⟩)
      g (c : 𝒪[k]) hc0 ⟨Matrix.of fun i j => G (i, j), by
        ext i j
        exact hG (i, j)⟩
  exact Set.mem_iUnion.2 ⟨⟨a, ha⟩, DoubleCoset.mem_doubleCoset.2 ⟨k₁, h₁, k₂, h₂,
    Units.ext (by rw [e, Units.val_mul, Units.val_mul, val_torusElt])⟩⟩
end GlobalTheory.GLDoubling
