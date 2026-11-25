-- Prove2me | solution 1 for GlobalTheory.AnArc.quasiPeriodic_and_independent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:33:25.508791+00:00
-- url     : https://prove2.me/submissions/adb08e52-39dc-4c22-9f3f-b052776c3120

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_CoeffFSumDerivEqFderiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_FormalThetaSumShiftPeriodDiv
import Theorems.Thm_GlobalTheory_AnArc_lin_Pw_sub
import Theorems.Thm_GlobalTheory_AnArc_perFactor_eq_exp
import Theorems.Thm_GlobalTheory_AnArc_perFactor_cocycle
import Theorems.Thm_GlobalTheory_AnArc_perFactor_comm
import Theorems.Thm_GlobalTheory_AnArc_summable_add_Pw_iff
import Theorems.Thm_GlobalTheory_AnArc_shift_comm
import Theorems.Thm_GlobalTheory_AnArc_shift_bijOn
import Theorems.Thm_GlobalTheory_AnArc_summable_add_Pw_div_iff
import Theorems.Thm_GlobalTheory_AnArc_Sum_add_Pw_div_mul
import Theorems.Thm_GlobalTheory_AnArc_FSumShift_eq
import Theorems.Thm_GlobalTheory_AnArc_eq_zero_of_sum_Sum
import Theorems.Thm_GlobalTheory_AnArc_eq_zero_of_sum_FSum
import Theorems.Thm_GlobalTheory_AnArc_Sum_add_period


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)
namespace GlobalTheory.AnArc
theorem _root_.solution :
    ((∀ w la v, A.perFactor w la v = Complex.exp (A.lin la v + A.logConst w la)) ∧
      (∀ w la la' v, A.perFactor w (la + la') v = A.perFactor w la (v + A.Pw w la') * A.perFactor w la' v) ∧
      (∀ w la la' v, A.perFactor w la (v + A.Pw w la') * A.perFactor w la' v = A.perFactor w la' (v + A.Pw w la) * A.perFactor w la v) ∧
      (∀ w la la', A.lin la (A.Pw w la') - A.lin la' (A.Pw w la) = -(2 * Real.pi * Complex.I * A.EF la la')) ∧
      ∀ j α, ∀ th ∈ A.Theta j α, ∀ w la v,
        ((Summable fun μ => A.term j α th μ (v + A.Pw w la) * eTwoPi (w * A.exponent j α μ)) ↔
          Summable fun μ => A.term j α th μ v * eTwoPi (w * A.exponent j α μ)) ∧
        A.Sum j α th w (v + A.Pw w la) = A.perFactor w la v ^ j * A.Sum j α th w v) ∧
    (∀ (k : ℕ) [NeZero k],
      (∀ la α th z, A.shift k la α th z =
        eTwoPi ((A.T la.y α + la.n α - A.H (A.ct α) la.l / (2 * Complex.I)) / k) *
          Complex.exp (-(Real.pi * A.H z la.l)) * th (z + (k : ℂ)⁻¹ • (A.ct la.y + la.l))) ∧
      (∀ la α, Set.BijOn (A.shift k la α) (A.Theta k α) (A.Theta k (α + la.y))) ∧
      (∀ la la' α th, A.shift k la (α + la'.y) (A.shift k la' α th) =
        eTwoPi (-(A.EF la la' / k)) • A.shift k la' (α + la.y) (A.shift k la α th)) ∧
      (∀ w la α th v,
        ((Summable fun μ => A.term k α th μ (v + (k : ℂ)⁻¹ • A.Pw w la) * eTwoPi (w * A.exponent k α μ)) ↔
          Summable fun μ =>
            A.term k (α + la.y) (A.shift k la α th) μ v * eTwoPi (w * A.exponent k (α + la.y) μ)) ∧
        A.Sum k α th w (v + (k : ℂ)⁻¹ • A.Pw w la) * eTwoPi (v.1 la.y) =
          Complex.exp (Real.pi * A.H v.2 la.l) * eTwoPi (w * A.be la.y α / k) *
            A.Sum k (α + la.y) (A.shift k la α th) w v) ∧
      ∀ (la : A.La) α (m : ℤ), A.be la.y α = k * m → ∀ th v, A.FSumShift k α th la v =
        HahnSeries.single m (Complex.exp (A.lin la v)) * A.FSum k (α + la.y) (A.shift k la α th) v) ∧
    ∀ (j : ℕ) [NeZero j] (C : Type) (I : C → Type) [Fintype C] [∀ c, Fintype (I c)] (rep : C → A.X),
      (∀ c c' μ, rep c = rep c' + j • μ → c = c') →
      ∀ th : ∀ c, I c → (Fin A.gB → ℂ) → ℂ, (∀ c, LinearIndependent ℂ (th c)) →
        (∀ r : ∀ c, I c → LaurentSeries ℂ,
          (∀ v, ∑ c, ∑ i, r c i * A.FSum j (rep c) (th c i) v = 0) → ∀ c i, r c i = 0) ∧
        ∀ w : ℂ, (∀ c i v, Summable fun μ => A.term j (rep c) (th c i) μ v * eTwoPi (w * A.exponent j (rep c) μ)) →
          ∀ r : ∀ c, I c → ℂ, (∀ v, ∑ c, ∑ i, r c i * A.Sum j (rep c) (th c i) w v = 0) → ∀ c i, r c i = 0 :=
  ⟨⟨A.perFactor_eq_exp, A.perFactor_cocycle, A.perFactor_comm, A.lin_Pw_sub,
      fun _ _ _ h w la v => ⟨A.summable_add_Pw_iff h w la v, A.Sum_add_period h w la v⟩⟩,
    fun k _ => ⟨A.shift_apply k, A.shift_bijOn k, A.shift_comm k,
      fun w la α th v => ⟨A.summable_add_Pw_div_iff k w la α th v, A.Sum_add_Pw_div_mul k w la α th v⟩,
      fun la _ _ hm th v => A.FSumShift_eq k la hm th v⟩,
    fun j _ _ _ _ _ _ hrep _ hth => ⟨fun _ h => A.eq_zero_of_sum_FSum hrep hth h,
      fun _ hs _ h => A.eq_zero_of_sum_Sum (NeZero.ne j) hrep hth (fun c i _ => hs c i _) h⟩⟩
end GlobalTheory.AnArc
