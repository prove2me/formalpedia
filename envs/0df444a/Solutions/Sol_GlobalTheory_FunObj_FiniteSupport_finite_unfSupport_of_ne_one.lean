-- Prove2me | solution 1 for GlobalTheory.FunObj.FiniteSupport.finite_unfSupport_of_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:30:08.945388+00:00
-- url     : https://prove2.me/submissions/1d231dd4-8824-42b7-8d7e-75b80c97101e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CharEqOneOfOpENeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierJacobiUnipotentEqProdRootExchange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteUnfSupportOfNeOne
import Theorems.Thm_GlobalTheory_FunObj_FiniteSupport_exists_rowR_mul
import Theorems.Thm_GlobalTheory_FunObj_FiniteSupport_finite_image_mk
import Theorems.Thm_GlobalTheory_FunObj_FiniteSupport_exists_unit_bd
import Theorems.Thm_GlobalTheory_FunObj_onColumn_apply
import Theorems.Thm_GlobalTheory_RootEx_Supp_isCompact_bd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.FunObj GlobalTheory.FunObj.FiniteSupport
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.RootEx.Supp GlobalTheory.RootEx.FJUnipotent
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [MeasurableSpace k] [BorelSpace k] {G : Grid k} {hs : 1 ≤ G.s} {ψ : AddChar k Circle} (ν : Measure k)
  [ν.IsAddHaarMeasure]
namespace GlobalTheory.FunObj.FiniteSupport
theorem _root_.solution (hψ : ψ ≠ 1) {ϖ : kˣ} {e : ℕ} {T : G.Args → ℂ}
    (hT : G.IsTensor ϖ e (oppositePath G.m) T) {J : G.Level}
    (hJ : ∀ j, 0 < j → j < G.m → IsOpen (J (G.m, j) : Set (GL (Fin (G.rank (G.m, j))) k)))
    (keep : Bool) (ρ : Reps hs J) : (unfSupport ψ ν keep ρ T).Finite := by
  have step : ∀ i : Fin (G.m - 2), ((fun β => ρ.elt β (G.m, i)) '' unfSupport ψ ν keep ρ T).Finite →
      ((fun β => β i) '' unfSupport ψ ν keep ρ T).Finite := by
    intro i hi
    obtain ⟨s, hs'⟩ := exists_unit_bd hi
    obtain ⟨δ, hδ⟩ := exists_rowR_mul hs ψ ν hψ hT s
    refine (finite_image_mk (rowR hs (j := i + 1) (by omega)) _ (hJ (i + 1) (by omega) (by omega))
      (isCompact_bd δ)).subset ?_
    rintro _ ⟨β, hβ, rfl⟩
    obtain ⟨x, hx⟩ := Function.ne_iff.1 hβ
    obtain ⟨y, hy⟩ := Function.ne_iff.1 hx
    obtain ⟨b1, b2⟩ := hs' _ ⟨β, hβ, rfl⟩
    obtain ⟨r, hr, w, w1, w2, hw⟩ := hδ keep (ρ.elt β) x y i i.2 hy b1 b2
    refine ⟨w, ⟨w1, w2⟩, ?_⟩
    rw [Reps.elt, onColumn_apply] at hw
    simp only [i.2, dif_pos] at hw
    refine Eq.trans ?_ (ρ.mk_rep i (β i))
    exact (DoubleCoset.eq _ _ _ _).2 ⟨r, hr, 1, one_mem _, by rw [mul_one]; exact hw⟩
  have col : ∀ j, j ≤ G.m - 2 → ((fun β => ρ.elt β (G.m, j)) '' unfSupport ψ ν keep ρ T).Finite := by
    intro j
    induction j with
    | zero =>
      refine fun _ => (Set.finite_singleton ρ.base).subset ?_
      rintro _ ⟨β, -, rfl⟩
      exact onColumn_apply _ 0
    | succ j ih =>
      intro hj
      refine ((step ⟨j, hj⟩ (ih (by omega))).image (ρ.rep ⟨j, hj⟩)).subset ?_
      rintro _ ⟨β, hβ, rfl⟩
      refine ⟨_, ⟨β, hβ, rfl⟩, ?_⟩
      simp only [Reps.elt, onColumn_apply, show j < G.m - 2 from hj, dif_pos]
  exact (Set.Finite.pi' fun i => step i (col i i.2.le)).subset fun β hβ i => ⟨β, hβ, rfl⟩
end GlobalTheory.FunObj.FiniteSupport
