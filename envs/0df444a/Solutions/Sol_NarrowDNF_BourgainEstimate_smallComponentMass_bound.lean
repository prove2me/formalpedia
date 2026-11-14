-- Prove2me | solution 1 for NarrowDNF.BourgainEstimate.smallComponentMass_bound
-- status  : ACCEPTED   (prove)
-- author  : @chenghua.liu
-- created : 2026-11-13T08:51:23.898395+00:00
-- url     : https://prove2.me/submissions/1ba49bcc-4af6-4ae2-a2f0-44a71ae8e332

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Logic.Equiv.Prod
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_BourgainComponents
import Definitions.Def_NarrowDNF_BourgainParameters
import Definitions.Def_NarrowDNF_Influence
import Theorems.Thm_NarrowDNF_BourgainEstimate_smallComponentMass_le_general
import Theorems.Thm_NarrowDNF_BourgainParameters_total_bound

namespace NarrowDNF.BourgainEstimate
end NarrowDNF.BourgainEstimate

namespace NarrowDNF.BourgainParameters
end NarrowDNF.BourgainParameters

section


/-! Explicit numerical choices for the reconstructed Bourgain small-component
estimate. The Fourier threshold eta retains the paper's constants. -/

noncomputable section
namespace NarrowDNF.BourgainParameters






private theorem cutoff_lower (k : ℕ) (e : ℝ) : realCutoff k e ≤ (cutoff k e : ℝ) :=
  Nat.le_ceil _

private theorem realCutoff_ge_one (k : ℕ) {e : ℝ} (he0 : 0 < e) (he1 : e ≤ 1) :
    1 ≤ realCutoff k e := by
  unfold realCutoff
  apply (le_div_iff₀ (pow_pos he0 10)).mpr
  simp only [one_mul]
  exact (pow_le_one₀ he0.le he1).trans (one_le_pow₀ (by norm_num))



















end NarrowDNF.BourgainParameters

end

end

noncomputable section
open scoped BigOperators
open NarrowDNF
open NarrowDNF.BourgainEstimate
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Complete natural-cutoff small-component estimate with exactly the paper's
Fourier threshold, including the stronger factor-two error margin. -/
theorem solution {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → Bool) {k : ℕ} (hk : 5 ≤ k) {e C : ℝ}
    (he : 0 < e) (he1 : e ≤ 1) (hC0 : 0 ≤ C) (hC : C ≤ k)
    (hI : Influence.totalInfluence p f ≤ C) :
    BourgainComponents.smallComponentMass p (fun x => Influence.boolValue (f x)) k
      (BourgainParameters.eta k e) ≤ e^2/(2*(k : ℝ)) := by
  have hM : 0 < BourgainParameters.cutoff k e := by
    have hge : (1 : ℝ) ≤ (BourgainParameters.cutoff k e : ℝ) :=
      (BourgainParameters.realCutoff_ge_one k he he1).trans
        (BourgainParameters.cutoff_lower k e)
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hge)
  have hτ : 0 < BourgainParameters.tau k e := by
    unfold BourgainParameters.tau
    positivity
  exact (smallComponentMass_le_general hp0 hp1 f k
    (BourgainParameters.cutoff k e) hM (BourgainParameters.eta k e)
    (BourgainParameters.tau k e) C hτ hC0 hI).trans
      (BourgainParameters.total_bound hk he he1 hC0 hC)
