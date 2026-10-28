-- Prove2me | solution 1 for OAI.TraceReconstruction.actual_one_window_oracle
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T09:58:45.065604+00:00
-- url     : https://prove2.me/submissions/7e7e8a1e-567c-40b0-be3c-a6a003517982

import Mathlib
import Definitions.Def_OAIQ9Tr002
import Theorems.Thm_OAI_TraceReconstruction_actual_source_oracle

section
-- module Solutions.OAIQ9_TR.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Patterns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Patterns

Pattern serialization, motif norms, flag posteriors, signed rank coefficients, translated binomials, and support geometry.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section


namespace TraceReconstruction

theorem atomString_append (n m : ℕ) (w : Bool → List Bool) (θ : Fin (n+m) → Bool) :
    atomString (n+m) w θ =
      atomString n w (fun i => θ (i.castLE (Nat.le_add_right n m))) ++
      atomString m w (fun i => θ (i.natAdd n)) := by
  simp only [atomString,List.ofFn_add,List.flatten_append]

theorem atomString_three (n m k : ℕ) (w : Bool → List Bool) (θ : Fin (n+m+k) → Bool) :
    atomString (n+m+k) w θ =
      atomString n w (fun i => θ ⟨i.val,by omega⟩) ++
      atomString m w (fun i => θ ⟨n+i.val,by omega⟩) ++
      atomString k w (fun i => θ ⟨n+m+i.val,by omega⟩) := by
  rw [atomString_append,atomString_append]
  rfl

end TraceReconstruction


end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Amplification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Amplification

Oracle products, mixed powers, padding, warmup and nested template Hellinger estimates, overlap, and block assembly.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section



noncomputable section



noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Literal template equality under deterministic pure residual padding. -/
theorem complementaryWords_pad (L P R a len : ℕ) (sign : Fin len → Bool)
    (w : Bool → List Bool) (τ : Bool) (hfit : a+len ≤ P) :
    complementaryWords (L+P+R) (L+a) len sign w τ =
      pureAtomRun (w false) L++complementaryWords P a len sign w τ++pureAtomRun (w false) R := by
  unfold complementaryWords
  rw [atomString_three]
  have hp (i : Fin L) : templateType (L+P+R) (L+a) len sign τ ⟨i.val,by omega⟩=false := by
    have hi := i.isLt
    simp only [templateType,dite_eq_right (by omega : ¬(L+a ≤ i.val ∧ i.val < L+a+len))]
  have hm (i : Fin P) : templateType (L+P+R) (L+a) len sign τ ⟨L+i.val,by omega⟩=
      templateType P a len sign τ i := by
    unfold templateType
    split_ifs with h h' h'
    · congr 2
      apply Fin.ext
      simp only
      omega
    · simp only at h
      omega
    · simp only at h
      omega
    · rfl
  have hr (i : Fin R) : templateType (L+P+R) (L+a) len sign τ ⟨L+P+i.val,by omega⟩=false := by
    simp only [templateType,dite_eq_right (by omega : ¬(L+a ≤ L+P+i.val ∧ L+P+i.val < L+a+len))]
  simp_rw [hp,hm,hr]
  change coordinateWord (fun _ : Fin L => w false)++_++coordinateWord (fun _ : Fin R => w false)=_
  rw [coordinateWord_constant,coordinateWord_constant]

theorem centeredResidual_geometry {N P : ℕ} (hP : 2 ≤ P) (hN : P ≤ N) :
    centeredLeftResidual N P+P+centeredRightResidual N P=N ∧
    centeredLeftResidual N P+(P/2-1)=N/2-1 := by
  simp only [centeredRightResidual,centeredLeftResidual]
  omega

/-- The auxiliary one-window oracle is centered at the same actual source
 motif after appending pure residuals, also for odd ambient atom counts. -/
theorem centeredComplementaryWords_pad (N P s : ℕ) (w : Bool → List Bool) (τ : Bool)
    (hP : 2 ≤ P) (hN : P ≤ N) (hfit : P/2-1+2^s ≤ P) :
    complementaryWords N (N/2-1) (2^s) (prouhetBool s) w τ =
      pureAtomRun (w false) (centeredLeftResidual N P)++
      complementaryWords P (P/2-1) (2^s) (prouhetBool s) w τ++
      pureAtomRun (w false) (centeredRightResidual N P) := by
  have h := complementaryWords_pad (centeredLeftResidual N P) P (centeredRightResidual N P)
    (P/2-1) (2^s) (prouhetBool s) w τ hfit
  rw [(centeredResidual_geometry hP hN).1,(centeredResidual_geometry hP hN).2] at h
  exact h

end TraceReconstruction



noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- The source's special one-window warmup observation. The ambient word
 need not have the root's arithmetic divisibility: exact pure residuals
 restore its literal center, at no additional statistical error. -/
theorem actual_one_window_oracle_oai {q E V : ℝ} {x y : List Bool} {k : ℕ}
    (C : OracleTracePair q x y k E V) (hq : q∈Set.Icc 0 1) (hE : 0 ≤ E)
    (s N T t h R : ℕ) (hT : 24 ≤ T) (he : Even T)
    (hMotif : 24*2^s ≤ T) (hroot : 4*(t+1) ≤ T)
    (hfit : t*(2*h+1)+T ≤ N)
    (ω a η L : ℝ) (ha : 0 < a) (hL : 0 < L) (hω : ω∈Set.Ioo 0 1)
    (hov : ω ≤ listTraceOverlap q hq (pureAtomRun x h) (pureAtomRun x (h+1)))
    (hk : 1 ≤ k) (hV : V ≤ L^2)
    (hscale : ((6*(2*k:ℕ):ℝ)*L)^2*sourceSparseCount (fun _ => T) s 0 ≤ 1/2)
    (hη : hiddenSmoothingBound t s ω ≤ η)
    (herror : sourceClippingCost (fun _ => T) (fun _ => t) s 0 k ω a L ≤ 1/2) :
    Nonempty (OracleTracePair q
      (complementaryWords N (N/2-1) (2^s) (prouhetBool s) (fun τ => if τ then y else x) false)
      (complementaryWords N (N/2-1) (2^s) (prouhetBool s) (fun τ => if τ then y else x) true) k
      (sourceClippingCost (fun _ => T) (fun _ => t) s 0 k ω a L+(T:ℝ)*E)
      (64*sourceSharpEnergyBudget (fun _ => T) (fun _ => t) s 0 R ω η a ((6*(2*k:ℕ):ℝ)*L))) := by
  let := C.finiteOutcome
  let p := t*(2*h+1)+T
  let atom : Bool → List Bool := fun τ => if τ then y else x
  have H : SourceLayoutMargins s (fun _ => p) (fun _ => T) (fun _ => t) (fun _ => h) 0 := by
    constructor <;> intro j hj <;> omega
  have hm : C.first.expect (fun z => |C.score z|^(2*k)) ≤ L^(2*k) := by
    have hv := C.first.expect_even_pow_le_of_moment C.score k hk (C.moment.trans hV)
    simpa only [pow_mul] using hv
  obtain ⟨W⟩ := actual_source_oracle hq hE s (fun _ => p) (fun _ => T) (fun _ => t)
    (fun _ => h) atom 0 R k H (fun _ => by omega) rfl
    (fun j hj => by omega) (fun _ _ => hT) (fun _ _ => he) (fun _ _ => hMotif) hroot
    C.first C.second C.decode C.score C.density C.likelihood_nonneg
    C.first_simulation C.second_simulation ω a η L ha hL hω
    (fun j hj => by
      have hj' : j=0 := by omega
      subst j
      exact hov)
    hk hm hscale (fun _ _ => hη) herror
  have hp : 2 ≤ p := by dsimp [p]; omega
  have hmp : p/2-1+2^s ≤ p := by dsimp [p] at *; omega
  let U := pureAtomRun x (centeredLeftResidual N p)
  let B := pureAtomRun x (centeredRightResidual N p)
  have heq (τ : Bool) := centeredComplementaryWords_pad N p s atom τ hp hfit hmp
  have HH := W.pad hq U B
  simp only [sourceBlockWord,sourceFitTail,add_zero] at HH
  change OracleTracePair q
    (U++complementaryWords p (p/2-1) (2^s) (prouhetBool s) atom false++B)
    (U++complementaryWords p (p/2-1) (2^s) (prouhetBool s) atom true++B) k _ _ at HH
  have hleft : U++complementaryWords p (p/2-1) (2^s) (prouhetBool s) atom false++B =
      complementaryWords N (N/2-1) (2^s) (prouhetBool s) atom false := (heq false).symm
  have hright : U++complementaryWords p (p/2-1) (2^s) (prouhetBool s) atom true++B =
      complementaryWords N (N/2-1) (2^s) (prouhetBool s) atom true := (heq true).symm
  rw [hleft,hright] at HH
  have hc : SourceLeafCount (fun _ => T) 1=T := by
    calc
      _ = Fintype.card (Fin (T*1)) := Fintype.card_congr finProdFinEquiv
      _ = T := by simp
  simp only [hc] at HH
  exact ⟨HH⟩

end TraceReconstruction



end
end
end
end
end

end OAI
end

theorem solution : type_of% @OAI.TraceReconstruction.actual_one_window_oracle_oai := @OAI.TraceReconstruction.actual_one_window_oracle_oai
