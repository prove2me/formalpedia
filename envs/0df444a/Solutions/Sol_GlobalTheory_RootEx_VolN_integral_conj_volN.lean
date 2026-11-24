-- Prove2me | solution 1 for GlobalTheory.RootEx.VolN.integral_conj_volN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:36:00.292283+00:00
-- url     : https://prove2.me/submissions/8db24c8e-790c-4cb0-ab3e-6ff8d52359db

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentHaarAndModulus
import Theorems.Thm_GlobalTheory_RootEx_VolN_conj_mkNel
import Theorems.Thm_GlobalTheory_RootEx_VolN_det_lm_embX
import Theorems.Thm_GlobalTheory_RootEx_VolN_det_rm_embX
import Theorems.Thm_GlobalTheory_RootEx_VolN_volN_eq
import Theorems.Thm_GlobalTheory_SplitWeil_integral_comp_mulVec_eq_smul
import Theorems.Thm_P2M_GlobalTheory_SplitWeil_nabs_pos__162ed63212bf


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.VolN
open GlobalTheory.RootEx.Model
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
variable [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure]
namespace GlobalTheory.RootEx.VolN
theorem _root_.solution {p : ℕ} (h1 : 1 ≤ p) (hp : p ≤ c) (x : GL n k) (f : GL (n ⊕ Fin c) k → ℂ) :
    ∫ u : N k n c p, f (embX c x * (u : GL (n ⊕ Fin c) k) * (embX c x)⁻¹) ∂(volN ν n c p) =
      (nabs k (Matrix.GeneralLinearGroup.det x) ^ (-((c : ℝ) + 1 - 2 * p))) •
        ∫ u : N k n c p, f u ∂(volN ν n c p) := by
  let d : kˣ := Matrix.GeneralLinearGroup.det x
  let u : kˣ := d⁻¹ ^ (p - 1) * d ^ (c - p)
  have hu : (rm (Up n c p) (embX c x⁻¹).val * lm (Up n c p) (embX c x).val).det = (u : k) := by
    rw [det_mul, det_lm_embX, det_rm_embX hp]; simp [u, d]
  let G : GL (Ix n c p) k := Matrix.GeneralLinearGroup.mkOfDetNeZero _ (hu ▸ u.ne_zero)
  have hG : Matrix.GeneralLinearGroup.det G = u := Units.ext hu
  have key := integral_comp_mulVec_eq_smul ν G (fun e => f (mkNel p e : N k n c p))
  rw [volN_eq, integral_map_equiv, integral_map_equiv]
  change ∫ e, f (embX c x * ((mkNel p e : N k n c p) : GL (n ⊕ Fin c) k) * (embX c x)⁻¹) ∂_ = _
  simp_rw [conj_mkNel]
  refine key.trans ?_
  rw [hG]
  congr 1
  have hd := nabs_pos' d
  have : nabs k u = (nabs k d)⁻¹ ^ (p - 1) * nabs k d ^ (c - p) := by simp [u, nabs]
  rw [this, mul_inv, inv_pow, inv_inv, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_neg hd.le,
    ← Real.rpow_add hd, Nat.cast_sub h1, Nat.cast_sub hp]
  congr 1
  push_cast; ring
end GlobalTheory.RootEx.VolN
