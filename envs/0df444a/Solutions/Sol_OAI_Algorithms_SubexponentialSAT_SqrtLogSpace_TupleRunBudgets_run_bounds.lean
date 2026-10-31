-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TupleRunBudgets.run_bounds
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T12:05:34.399733+00:00
-- url     : https://prove2.me/submissions/04272957-c331-40d9-950e-05339dd32719

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S191

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_AttainedSignatures
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFinite _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# First occurrences of attained keys

The subtype below is a specification of emissions, not a stored family.
The executable scan checks a candidate against its predecessors one at a time.
The key may be an entire integer row-signature; no coordinate projection occurs.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatures

variable {N : ℕ} {κ : Type*} (key : Fin N → κ)

theorem representative_exists (hN : 0 < N) : Nonempty (Representative key) :=
  ⟨⟨⟨0, hN⟩, by intro j hj; exact (Nat.not_lt_zero _ hj).elim⟩⟩

theorem card_representative_pos (hN : 0 < N) : 0 < Nat.card (Representative key) := by
  let _ := representative_exists key hN
  exact Nat.card_pos

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatures
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpUnaryRangeProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed unary range enumerator which physically emits every framed index. -/
namespace SubexponentialSAT.SubexpUnaryRangeProgram

open BitProgram StructuredCalls SubexpIncidencePlanPrimitives

theorem steps_le (j n : ℕ) : 1 + steps j n ≤ n * (12*(j+n)+23) + 2 := by
  induction n generalizing j with
  | zero => simp [steps]
  | succ n ih =>
      have h := ih (j+1)
      simp only [steps]
      nlinarith

end SubexponentialSAT.SubexpUnaryRangeProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_TruncatedRingProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Native arithmetic after immediate Boolean specialization

The existing finite sparse-product program is used with empty formal support.
Its keys still carry the ambient input coordinate type; this does not compress
the declared variables. There are at most `u * J` retained entries, including
zero cutoffs. Polynomial local time therefore bounds all its source prefixes,
including the table, inputs, output, normalization copies and arithmetic scratch.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram

open scoped BigOperators
open OAI OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open MomentsProgram BitProgram

/- The two fields coincide with LeafProgram.NativeSemantics.Good. The
arithmetic layer states them transparently to avoid importing the factor
interpreter. Conversion in either direction supplies `valid` and `nodup`.
The proof bodies below are the original finite-program validity arguments. -/

variable {V R : Type*} [DecidableEq V] [CommRing R]

private theorem localBudget_mono (n B d u J N a : ℕ)
    (hn : n ≤ a) (hB : B ≤ a) (hd : d ≤ a) (hu : u ≤ a) (hJ : J ≤ a) (hN : N ≤ a) :
    localBudget n B d u J N ≤ localBudget a a a a a a := by
  dsimp [localBudget, normalizationBudget, additionBudget, scalingBudget, productBudget,
    Product.stepEnvelope, MomentsReadoutProgram.uniformReadoutBudget,
    MomentsReadoutProgram.uniformSlotBudget, Dictionary.codeBranchBudget]
  gcongr

/-- The degree and constant are fixed before every runtime dimension. -/
theorem localBudget_le (n B d u J N : ℕ) :
    localBudget n B d u J N ≤ 3000000 * (n + B + d + u + J + N + 1) ^ 10 := by
  let a := n + B + d + u + J + N + 1
  have ha : 1 ≤ a := by dsimp [a]; omega
  refine (localBudget_mono n B d u J N a (by dsimp [a]; omega) (by dsimp [a]; omega)
    (by dsimp [a]; omega) (by dsimp [a]; omega) (by dsimp [a]; omega)
    (by dsimp [a]; omega)).trans ?_
  change localBudget a a a a a a ≤ 3000000 * a ^ 10
  have h0 : 1 ≤ a ^ 10 := Nat.one_le_pow 10 a ha
  have h1 : a ≤ a ^ 10 := by simpa using pow_le_pow_right' ha (show 1 ≤ 10 by decide)
  have h2 : a ^ 2 ≤ a ^ 10 := pow_le_pow_right' ha (by decide)
  have h3 : a ^ 3 ≤ a ^ 10 := pow_le_pow_right' ha (by decide)
  have h4 : a ^ 4 ≤ a ^ 10 := pow_le_pow_right' ha (by decide)
  have h5 : a ^ 5 ≤ a ^ 10 := pow_le_pow_right' ha (by decide)
  have h6 : a ^ 6 ≤ a ^ 10 := pow_le_pow_right' ha (by decide)
  have h7 : a ^ 7 ≤ a ^ 10 := pow_le_pow_right' ha (by decide)
  have h8 : a ^ 8 ≤ a ^ 10 := pow_le_pow_right' ha (by decide)
  have h9 : a ^ 9 ≤ a ^ 10 := pow_le_pow_right' ha (by decide)
  dsimp [localBudget, normalizationBudget, additionBudget, scalingBudget, productBudget,
    Product.stepEnvelope, MomentsReadoutProgram.uniformReadoutBudget,
    MomentsReadoutProgram.uniformSlotBudget, Dictionary.codeBranchBudget]
  ring_nf
  omega

theorem additionBudget_le_local (n B d u J N : ℕ) :
    additionBudget n B d u J ≤ localBudget n B d u J N := by
  unfold localBudget
  omega

theorem productBudget_le_local (n B d u J N : ℕ) :
    productBudget n B d u J ≤ localBudget n B d u J N := by
  unfold localBudget
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorProductSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The original concrete factor accumulator, with empty correction support.
All three tape moves and the original sparse product call are charged. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorProductSpace

open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open SqrtLog SqrtLog.LeafProgram MomentsProgram

/-- The degree and constant are fixed independently of all input dimensions. -/
theorem budget_polynomial (n B d u J : ℕ) :
    budget n B d u J ≤ 4000000 * (n + B + d + u + J + 1) ^ 10 := by
  let a := n + B + d + u + J + 1
  have ha : 1 ≤ a := by dsimp [a]; omega
  have hn : n ≤ a := by dsimp [a]; omega
  have hB : B ≤ a := by dsimp [a]; omega
  have hd : d ≤ a := by dsimp [a]; omega
  have hu : u ≤ a := by dsimp [a]; omega
  have hJ : J ≤ a := by dsimp [a]; omega
  have hm : byteBound n B d u J ≤ byteBound a a a a a := by
    dsimp only [byteBound]
    gcongr
  have hdiag : byteBound a a a a a = 2 * a ^ 4 + 6 * a ^ 3 + 2 * a ^ 2 := by
    unfold byteBound
    ring
  have h2 : a ^ 2 ≤ a ^ 10 := Nat.pow_le_pow_right ha (by decide)
  have h3 : a ^ 3 ≤ a ^ 10 := Nat.pow_le_pow_right ha (by decide)
  have h4 : a ^ 4 ≤ a ^ 10 := Nat.pow_le_pow_right ha (by decide)
  have h0 : 1 ≤ a ^ 10 := Nat.one_le_pow 10 a ha
  rw [hdiag] at hm
  have hp := (TruncatedRingProgram.productBudget_le_local n B d u J 0).trans
    (TruncatedRingProgram.localBudget_le n B d u J 0)
  simp only [Nat.add_zero] at hp
  change TruncatedRingProgram.productBudget n B d u J ≤ 3000000 * a ^ 10 at hp
  change budget n B d u J ≤ 4000000 * a ^ 10
  unfold budget
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorProductSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryIncidenceSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace

open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open MomentsProgram TruncatedRingProgram
open scoped BigOperators

/-- Uniform scalar envelope for the actual shifted-row work. -/
theorem rowWork_polynomial (N J n d B A : ℕ)
    (hN : N ≤ A) (hJ : J ≤ A) (hn : n ≤ A) (hd : d ≤ A) (hB : B ≤ A)
    (ha : 1 ≤ A) : PerturbationAssembly.rowWorkPolynomial N J n d B ≤ 100000000 * A ^ 9 := by
  have hm : PerturbationAssembly.rowWorkPolynomial N J n d B ≤ PerturbationAssembly.rowWorkPolynomial A A A A A := by
    unfold PerturbationAssembly.rowWorkPolynomial DensePolynomialProgram.AddService.budget
    gcongr
  have h0 : 1 ≤ A ^ 9 := Nat.one_le_pow 9 A ha
  have h1 : A ≤ A ^ 9 := by simpa using pow_le_pow_right' ha (show 1 ≤ 9 by decide)
  have h2 : A ^ 2 ≤ A ^ 9 := pow_le_pow_right' ha (by decide)
  have h3 : A ^ 3 ≤ A ^ 9 := pow_le_pow_right' ha (by decide)
  have h4 : A ^ 4 ≤ A ^ 9 := pow_le_pow_right' ha (by decide)
  have h5 : A ^ 5 ≤ A ^ 9 := pow_le_pow_right' ha (by decide)
  have h6 : A ^ 6 ≤ A ^ 9 := pow_le_pow_right' ha (by decide)
  have h7 : A ^ 7 ≤ A ^ 9 := pow_le_pow_right' ha (by decide)
  have h8 : A ^ 8 ≤ A ^ 9 := pow_le_pow_right' ha (by decide)
  apply hm.trans
  unfold PerturbationAssembly.rowWorkPolynomial DensePolynomialProgram.AddService.budget
  ring_nf
  omega


/-- The actual low emitter has a fixed tenth-degree budget in its concrete
row count, dense row length, truncation length, ring word widths and cache sizes. -/
theorem lowWork_polynomial (n N J t d E : ℕ) :
    PerturbationAssembly.lowWorkPolynomial n N J t d E ≤
      1000000000 * (n + N + J + d + baseWidth 3 t + E + 1) ^ 10 := by
  let B := baseWidth 3 t
  let A := n + N + J + d + B + E + 1
  have ha : 1 ≤ A := by dsimp [A]; omega
  have hn : n ≤ A := by dsimp [A]; omega
  have hN : N ≤ A := by dsimp [A]; omega
  have hJ : J ≤ A := by dsimp [A]; omega
  have hd : d ≤ A := by dsimp [A]; omega
  have hB : B ≤ A := by dsimp [A]; omega
  have hE : E ≤ A := by dsimp [A]; omega
  have hrow := rowWork_polynomial N J n d B A hN hJ hn hd hB ha
  have hm : PerturbationAssembly.lowWorkPolynomial n N J t d E ≤
      1000000*(A+1)*(A+1)*(A+1)^3*(A+1)^2 + (33*A+20*(A*A)+83) +
      (9*A+14*A+9*(A*(A*A))+7*(A*A)+440*(A+1)*(A*A+1)+47) +
      (7*(A*(2*(A*(A*A))+2)+1)+9*A+A*(100000000*A^9+2)+20) +
      (2*(2*(A*(A*A))+2*A+A*A)+6*A+33) + (2*(A*A)+3) := by
    unfold PerturbationAssembly.lowWorkPolynomial
    change 1000000*(n+1)*(N+1)*(d+1)^3*(B+1)^2 + (33*n+20*(d*B)+83) +
      (9*E+14*J+9*(J*(d*B))+7*(d*B)+440*(J+1)*(d*B+1)+47) +
      (7*(n*(2*(N*(d*B))+2)+1)+9*n+n*(PerturbationAssembly.rowWorkPolynomial N J n d B+2)+20) +
      (2*(2*(J*(d*B))+2*J+d*B)+6*E+33) + (2*(d*B)+3) ≤ _
    gcongr
  have h0 : 1 ≤ A ^ 10 := Nat.one_le_pow 10 A ha
  have h1 : A ≤ A ^ 10 := by simpa using pow_le_pow_right' ha (show 1 ≤ 10 by decide)
  have h2 : A ^ 2 ≤ A ^ 10 := pow_le_pow_right' ha (by decide)
  have h3 : A ^ 3 ≤ A ^ 10 := pow_le_pow_right' ha (by decide)
  have h4 : A ^ 4 ≤ A ^ 10 := pow_le_pow_right' ha (by decide)
  have h5 : A ^ 5 ≤ A ^ 10 := pow_le_pow_right' ha (by decide)
  have h6 : A ^ 6 ≤ A ^ 10 := pow_le_pow_right' ha (by decide)
  have h7 : A ^ 7 ≤ A ^ 10 := pow_le_pow_right' ha (by decide)
  change PerturbationAssembly.lowWorkPolynomial n N J t d E ≤ 1000000000 * A ^ 10
  apply hm.trans
  ring_nf
  omega


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorTableNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Physical source preparation for the specialized factor table. The old
master-word argument is generalized to the actually selected unary factor,
then transported through the fixed protected-port embedding. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative
open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram
open PerturbationAssembly LayoutProgram SubexpSetupStorage DensePolynomialProgram
open OAI.Algorithms.SubexponentialSAT.Subexp OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking OAI.Algorithms.SubexponentialSAT.MulticolorTypes
attribute [local simp] Fin.coe_ofNat_eq_mod

variable {r Q d n J S f : ℕ} {p : SourceBank.Parameters r Q d}
    {ps : List (ℕ × ℕ)} {P : PackingData (Fin ps.length) (UniversalType r Q 1)}
    {a : SourceReady.Data} {theta : DensePolynomialProgram.Coeff (baseWidth 3 p.t) d}

/-- The nested actual emitter and specializer budgets have a fixed degree,
independent of every runtime scalar, word, assignment and factor index. -/
theorem specializedWorkPolynomial_bound (t d u J N n S : ℕ) :
    specializedWorkPolynomial t d u J N n S ≤
      (3200000 * (1000000000*3^10+64)^10) *
        (n+N+J+d+baseWidth 3 t+u+S+1)^100 := by
  let A := n+N+J+d+baseWidth 3 t+u+S+1
  have hA : 1 ≤ A := by dsimp [A]; omega
  have hn : n ≤ A := by dsimp [A]; omega
  have hJ : J ≤ A := by dsimp [A]; omega
  have hd : d ≤ A := by dsimp [A]; omega
  have hB : baseWidth 3 t ≤ A := by dsimp [A]; omega
  have hu : u ≤ A := by dsimp [A]; omega
  have hS : S ≤ A := by dsimp [A]; omega
  have hj : J-1 ≤ A := (Nat.sub_le J 1).trans hJ
  have hlow := QueryProducerSpace.lowWork_polynomial n N J t d (3*S)
  have hlow' : lowWorkPolynomial n N J t d (3*S) ≤
      1000000000*(3*A)^10 := by
    apply hlow.trans
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    dsimp [A]
    omega
  have hm : lowWorkPolynomial n N J t d (3*S) + 3*S +
      specializedRawBound n u J (baseWidth 3 t) d + n + baseWidth 3 t + d + u + J +
      (1+n*(J-1)) + 1 ≤
      1000000000*(3*A)^10 + 3*A +
      (1+A*A)*(2*(A+A+A)+2*(A*A)+2) + A+A+A+A+A+(1+A*A)+1 := by
    unfold specializedRawBound
    gcongr
  have h0 : 1 ≤ A^10 := Nat.one_le_pow 10 A hA
  have h1 : A ≤ A^10 := by simpa using pow_le_pow_right' hA (show 1 ≤ 10 by decide)
  have h2 : A^2 ≤ A^10 := pow_le_pow_right' hA (by decide)
  have h3 : A^3 ≤ A^10 := pow_le_pow_right' hA (by decide)
  have h4 : A^4 ≤ A^10 := pow_le_pow_right' hA (by decide)
  have hinner : lowWorkPolynomial n N J t d (3*S) + 3*S +
      specializedRawBound n u J (baseWidth 3 t) d + n + baseWidth 3 t + d + u + J +
      (1+n*(J-1)) + 1 ≤ (1000000000*3^10+64)*A^10 := by
    apply hm.trans
    ring_nf
    omega
  have hp := Nat.mul_le_mul_left 3200000 (Nat.pow_le_pow_left hinner 10)
  simpa only [specializedWorkPolynomial,mul_pow,←pow_mul,
    show 10*10=100 from rfl,Nat.mul_assoc,A] using hp

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorAssignmentLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Relational execution of the fixed specialized factor-record loop. This
adapts the original FactorLoop reader/while proof to the shared 896-stack ABI
and empty-support dictionaries. The explicit callback premise must be proved
for the actual callback before this component can close an algorithm endpoint. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentLoop
attribute [local simp] Fin.coe_ofNat_eq_mod
open OAI BitProgram StructuredCalls SqrtLog SqrtLog.LeafProgram MomentsProgram

/-- A fixed fourth power suffices for the full stored-ID loop controller once
its concrete per-factor budget C and structural input length T are supplied. -/
theorem uniformProductBudget_polynomial (n B d u J T C : ℕ) :
    uniformProductBudget n B d u J T C ≤
      256 * (n + B + d + u + J + T + C + 1) ^ 4 := by
  let a := n + B + d + u + J + T + C + 1
  have ha : 1 ≤ a := by dsimp [a]; omega
  have hn : n ≤ a := by dsimp [a]; omega
  have hB : B ≤ a := by dsimp [a]; omega
  have hd : d ≤ a := by dsimp [a]; omega
  have hu : u ≤ a := by dsimp [a]; omega
  have hJ : J ≤ a := by dsimp [a]; omega
  have hT : T ≤ a := by dsimp [a]; omega
  have hC : C ≤ a := by dsimp [a]; omega
  have hm : uniformProductBudget n B d u J T C ≤
      uniformProductBudget a a a a a a a := by
    dsimp only [uniformProductBudget, byteBound]
    gcongr
  have he : uniformProductBudget a a a a a a a =
      32 * a ^ 4 + 96 * a ^ 3 + 33 * a ^ 2 + 25 * a + 35 := by
    unfold uniformProductBudget byteBound
    ring
  have h3 : a ^ 3 ≤ a ^ 4 := Nat.pow_le_pow_right ha (by decide)
  have h2 : a ^ 2 ≤ a ^ 4 := Nat.pow_le_pow_right ha (by decide)
  have h1 : a ≤ a ^ 4 := by simpa using Nat.pow_le_pow_right ha (show 1 ≤ 4 by decide)
  have h0 : 1 ≤ a ^ 4 := Nat.one_le_pow 4 a ha
  rw [he] at hm
  change uniformProductBudget n B d u J T C ≤ 256 * a ^ 4
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentLoop
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleDFS
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Attained-signature DFS cardinalities and work

A level is indexed by its attained signatures, not its Boolean assignments or
an ambient rectangular range of raw row values. These finite types describe
visits mathematically; no family or product is materialized by these definitions.
The native encoded-frame traversal is a separate refinement obligation.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleDFS

open scoped BigOperators

/-- Empty heads contribute one key, so every factor is at least one. -/
theorem prefixCount_le (K : ℕ → ℕ) {depth levels : ℕ} (hd : depth ≤ levels)
    (hK : ∀ i < levels, 1 ≤ K i) : prefixCount K depth ≤ prefixCount K levels := by
  apply Finset.prod_le_prod_of_subset_of_one_le' (Finset.range_mono hd)
  intro i hi _
  exact hK i (Finset.mem_range.mp hi)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleDFS
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryTupleSum
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete unsigned tuple accumulation. The complete head product on852
is normalized into the pair accumulator851. Physical caches are copied from
retained masters and every native peripheral scratch word is paid for. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleSum

open OAI BitProgram StructuredCalls SqrtLog SubexpLiftRing SubexpQuarticRing
open MomentsProgram TruncatedRingProgram

theorem budget_polynomial (n B d u J incoming : ℕ) :
    budget n B d u J incoming ≤
      75*incoming+97+3000000*(n+B+d+u+J+1)^10 := by
  have h := (additionBudget_le_local n B d u J 0).trans (localBudget_le n B d u J 0)
  simpa only [budget,Nat.add_zero] using Nat.add_le_add_left h (75*incoming+97)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleSum
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorAssignmentCorrect
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual initializer, source-context cache, dispatcher, specialized
incidence producer and factor arithmetic instantiate the stored-ID fold.
The output is the entire specialized coefficient-ring product on stack854.
Every resource assertion below concerns this same fixed command. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCorrect

open OAI BitProgram StructuredCalls SubexpSetupStorage
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram MomentsProgram
open OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open FactorAssignmentProgram FactorAssignmentBoundary FactorAssignmentLoop

noncomputable section
attribute [local simp] Fin.coe_ofNat_eq_mod

variable {r Q n d P M S : ℕ} {q : Factor.Spec r Q n d}

/-- The whole accepted-assignment budget is a fixed fourth power of the
explicit callback budget and structural dimensions. Composing the callback's
fixed polynomial keeps the exponent independent of the input. -/
theorem assignmentBudget_polynomial (q : Factor.Spec r Q n d) (P S Z : ℕ) :
    assignmentBudget q P S Z ≤
      1600 * (entryScratch.length + n + baseWidth 3 q.p.t + d + q.u + q.J + P +
        FactorAssignmentCallback.uniformCallbackBudget q P S Z + 1)^4 := by
  let C := FactorAssignmentCallback.uniformCallbackBudget q P S Z
  let X := entryScratch.length + n + baseWidth 3 q.p.t + d + q.u + q.J + P + C + 1
  have hX : 1 ≤ X := by dsimp [X]; omega
  have he : entryScratch.length ≤ X := by dsimp [X]; omega
  have hp : P ≤ X := by dsimp [X]; omega
  have hp1 : P+1 ≤ X := by dsimp [X]; omega
  have hb := uniformProductBudget_polynomial n (baseWidth 3 q.p.t) d q.u q.J P C
  have hc : entryScratch.length*(2*P+3) ≤ 5*X^2 := by
    have h : entryScratch.length*(2*P+3) ≤ X*(2*X+3) := by gcongr
    nlinarith
  have hy : n+baseWidth 3 q.p.t+d+q.u+q.J+P+C+1 ≤ X := by dsimp [X]; omega
  have hh : uniformProductBudget n (baseWidth 3 q.p.t) d q.u q.J P C ≤ 256*X^4 := by
    apply hb.trans
    gcongr
  have h1 : X ≤ X^4 := by simpa using Nat.pow_le_pow_right hX (show 1 ≤ 4 by decide)
  have h2 : X^2 ≤ X^4 := Nat.pow_le_pow_right hX (by decide)
  have h0 : 1 ≤ X^4 := Nat.one_le_pow _ _ hX
  change entryScratch.length*(2*P+3)+1100*(P+1)+2+
    uniformProductBudget n (baseWidth 3 q.p.t) d q.u q.J P C ≤ 1600*X^4
  omega

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCorrect
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowMismatchBound
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Bounds for the actual unary-range, mismatch-filter and type-extractor
programs used by the universal-row constructor. -/

namespace SubexponentialSAT.Subexp.UniversalRowMismatchBound

open MulticolorTypes
open MismatchPlanProgram (indexRecords callbackCost sourceBound)

theorem indexRecords_budget (width : ℕ) (positions : List ℕ) :
    RecordPrograms.budget (callbackCost width) (indexRecords positions) =
      (28 * width + 45) * positions.sum + (43 * width + 87) * positions.length := by
  induction positions with
  | nil => simp [indexRecords, RecordPrograms.budget]
  | cons i positions ih =>
      simp only [indexRecords, List.map_cons, RecordPrograms.budget, callbackCost,
        List.length_replicate, List.sum_cons, List.length_cons] at ih ⊢
      rw [ih]
      ring

theorem indexRecords_encoded_length (positions : List ℕ) :
    (ProgramEncoding.encodeRecords (indexRecords positions)).length =
      2 * positions.sum + 2 * positions.length + 1 := by
  simpa [indexRecords, List.map_map, Function.comp_def] using
    ProgramEncoding.encodeRecords_length (indexRecords positions)

theorem sourceBound_indexRecords (width : ℕ) (positions : List ℕ) :
    sourceBound width (indexRecords positions) =
      (28 * width + 65) * positions.sum + (43 * width + 107) * positions.length + 18 := by
  change 8 + RecordPrograms.budget (callbackCost width) (indexRecords positions) +
    10 * (ProgramEncoding.encodeRecords (indexRecords positions)).length = _
  rw [indexRecords_budget, indexRecords_encoded_length]
  ring

theorem sum_range_le_sq (Q : ℕ) : (List.range Q).sum ≤ Q ^ 2 := by
  induction Q with
  | zero => simp
  | succ Q ih =>
      rw [List.range_succ, List.sum_append, List.sum_singleton]
      nlinarith

theorem budget_le_polynomial (Q r : ℕ) :
    UniversalRowMismatchProgram.budget Q r ≤
      (28 * r + 77) * Q ^ 2 + (43 * r + 139) * Q + 32 := by
  have hrange := SubexpUnaryRangeProgram.steps_le 0 Q
  have hsum := Nat.mul_le_mul_left (28 * r + 65) (sum_range_le_sq Q)
  unfold UniversalRowMismatchProgram.budget
  rw [sourceBound_indexRecords]
  simp only [List.sum_reverse, List.length_reverse, List.length_range]
  simp only [Nat.zero_add] at hrange
  nlinarith only [hrange, hsum]

theorem budget_le (Q r S : ℕ) (hS : 1 ≤ S) (hQ : Q ≤ S) (hr : r ≤ S) :
    UniversalRowMismatchProgram.budget Q r ≤ mismatchBound S := by
  have h12 : S ≤ S ^ 2 := by nlinarith
  have h23 : S ^ 2 ≤ S ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  apply (budget_le_polynomial Q r).trans
  change _ ≤ 400 * S ^ 3
  calc
    _ ≤ (28 * S + 77) * S ^ 2 + (43 * S + 139) * S + 32 := by gcongr
    _ ≤ _ := by nlinarith only [hS, h12, h23]

end SubexponentialSAT.Subexp.UniversalRowMismatchBound

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorTableBudgets
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed polynomial bounds for the actual factor-table service. The scalar
allowance includes physical signed-word lengths; it never bounds the integer
value of an exponential modulus or numerator in unary. All ambient source
rows and every specialized incidence record are included. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableBudgets
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SubexpLiftRing
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.Polynomial
open OAI.Algorithms.SubexponentialSAT.Subexp
open FactorTableNative

private theorem value_table_le {r Q d : ℕ} (p : SourceBank.Parameters r Q d) (S : ℕ)
    (hr : r ≤ S) (hQ : Q ≤ S) (hd : d ≤ S) (ht : p.t ≤ S)
    (hR : p.R ≤ S) (hA : p.aWord.length ≤ S) (hW : p.width.length ≤ S)
    (hP : RowSelectionProgram.pairLength p.power ≤ S) :
    LayoutSourceValuesProgram.Native.polynomialBudget r Q p.aWord.length p.R
      p.width.length (RowSelectionProgram.pairLength p.power) p.t d ≤
    LayoutSourceValuesProgram.Native.polynomialBudget S S S S S S S S := by
  unfold LayoutSourceValuesProgram.Native.polynomialBudget
    LayoutSourceValuesProgram.Native.callbackBudget
    LayoutSourceValuesProgram.Native.integerBits IntegerRingLiftProgram.polynomialBudget
    LayoutSourceValuesProgram.Native.numeratorAllowance
    LayoutSourceValuesProgram.Native.scalarAllowance
    LayoutProgramScalar.FromCounts.binomialCost LayoutProgramScalar.numeratorPrepareCost
    LayoutProgramScalar.numeratorFoldCost LayoutProgramScalar.termGrowth
    MatrixExtendedEntryProgram.guardStageCost MatrixEntryProgram.scanStageCost
    CollisionProgram.typeWidth
  simp only [RingProgram.ternary_baseWidth]
  gcongr

private theorem source_bound_mono : Monotone UniversalRowSourceBound.sourceBound := by
  intro S T h
  unfold UniversalRowSourceBound.sourceBound UniversalRowSourceBound.dataBound
    UniversalRowSourceBound.outerLoopBound UniversalRowSourceBound.termBound
    UniversalRowSourceBound.factorLoopBound UniversalRowSourceBound.factorCallbackBound
    UniversalRowSourceBound.inputBound UniversalRowSourceBound.rowBytes
    UniversalRowSourceBound.termBytes UniversalRowSourceBound.factorsBytes
    UniversalRowSourceBound.factorBytes UniversalRowSourceBound.indicesBound
  gcongr

private theorem uniform_le {r Q d : ℕ} (p : SourceBank.Parameters r Q d) (E S : ℕ)
    (hE : E ≤ S) (hr : r ≤ S) (hQ : Q ≤ S) (hd : d ≤ S) (ht : p.t ≤ S)
    (hR : p.R ≤ S) (hA : p.aWord.length ≤ S) (hW : p.width.length ≤ S)
    (hP : RowSelectionProgram.pairLength p.power ≤ S) :
    SourceBank.uniformBudget p E ≤ uniformEnvelope S := by
  have hv := value_table_le p S hr hQ hd ht hR hA hW hP
  have hm := UniversalRowMismatchBound.budget_le Q r (S+1) (by omega)
    (by omega) (by omega)
  have he : UniversalRowMismatchTypes.extractBudget (r := r) (Q := Q) (0 : Fin 1) ≤
      UniversalRowMismatchTypes.extractBudget (r := S) (Q := S) (0 : Fin 1) := by
    unfold UniversalRowMismatchTypes.extractBudget CollisionProgram.typeWidth
    gcongr
  have hw : SourceBank.sourceWorkspace p E ≤ workspaceEnvelope S := by
    unfold SourceBank.sourceWorkspace workspaceEnvelope UniversalRowSourceBound.indicesBound
    simp only [RingProgram.ternary_baseWidth]
    gcongr
  have hs := source_bound_mono hw
  unfold SourceBank.uniformBudget uniformEnvelope
  gcongr

theorem source_work_le {r Q d : ℕ} (p : SourceBank.Parameters r Q d) (E S : ℕ)
    (hE : E ≤ S) (hr : r ≤ S) (hQ : Q ≤ S) (hd : d ≤ S) (ht : p.t ≤ S)
    (hR : p.R ≤ S) (hA : p.aWord.length ≤ S) (hW : p.width.length ≤ S)
    (hP : RowSelectionProgram.pairLength p.power ≤ S) :
    LeafProgram.Source.nativeSourceWorkPolynomial p E ≤ sourceEnvelope S := by
  have hu := uniform_le p E S hE hr hQ hd ht hR hA hW hP
  have hl : UniversalRowSourceBound.sourceLengthBound E ≤
      UniversalRowSourceBound.sourceLengthBound S := by
    unfold UniversalRowSourceBound.sourceLengthBound UniversalRowSourceBound.inputBound
      UniversalRowSourceBound.rowBytes UniversalRowSourceBound.termBytes
      UniversalRowSourceBound.factorsBytes UniversalRowSourceBound.factorBytes
    gcongr
  unfold LeafProgram.Source.nativeSourceWorkPolynomial nativeRowsPolynomial
    stagedSourceBudget nativeSourceBudget LeafProgram.Source.nativeOutputBound sourceEnvelope
    LayoutSourceRowsProgramInitialize.budget rowBudgetPolynomial
  simp only [RingProgram.ternary_baseWidth]
  gcongr

theorem payload_bound_le (n u J t d S : ℕ)
    (hn : n ≤ S) (hu : u ≤ S) (hJ : J ≤ S) (ht : t ≤ S) (hd : d ≤ S) :
    specializedPayloadBound n u J (baseWidth 3 t) d ≤ payloadEnvelope S := by
  unfold specializedPayloadBound payloadEnvelope
  simp only [RingProgram.ternary_baseWidth]
  rw [← Nat.mul_assoc 2 d (2*t)]
  gcongr

theorem specialization_work_le (t d u J R n E S : ℕ)
    (ht : t ≤ S) (hd : d ≤ S) (hu : u ≤ S) (hJ : J ≤ S)
    (hR : R ≤ S) (hn : n ≤ S) (hE : E ≤ S) :
    specializedWorkPolynomial t d u J (R+1) n E ≤ specializationEnvelope S := by
  apply (specializedWorkPolynomial_bound t d u J (R+1) n E).trans
  unfold specializationEnvelope
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  simp only [RingProgram.ternary_baseWidth]
  omega

theorem literal_work_le {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (u J n E H S : ℕ) (hu : u ≤ S) (hJ : J ≤ S) (hn : n ≤ S) (hE : E ≤ S)
    (hH : H ≤ S) (hr : r ≤ S) (hQ : Q ≤ S) (hd : d ≤ S) (ht : p.t ≤ S)
    (hR : p.R ≤ S) (hA : p.aWord.length ≤ S) (hW : p.width.length ≤ S)
    (hP : RowSelectionProgram.pairLength p.power ≤ S) :
    specializedLiteralWork p u J n E H ≤ literalEnvelope S := by
  have hsource := source_work_le p E S hE hr hQ hd ht hR hA hW hP
  have hspecial := specialization_work_le p.t d u J p.R n E S ht hd hu hJ hR hn hE
  have hpayload := payload_bound_le n u J p.t d S hn hu hJ ht hd
  unfold specializedLiteralWork literalEnvelope
  simp only [RingProgram.ternary_baseWidth] at hpayload ⊢
  gcongr

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableBudgets
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadEvaluationProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete correction-mask checking for a head rescan. This local routine
preserves its input masters and charges every stack at every source prefix. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.HeadGate
/-- A simple monomial envelope with a degree independent of every input. -/
theorem gatePolynomial_le (B : ℕ) : gatePolynomial B≤15000*(B+1)^6 := by
  dsimp [gatePolynomial,rowPolynomial,widthPolynomial]
  nlinarith only [Nat.zero_le B,Nat.zero_le (B^2),Nat.zero_le (B^3),
    Nat.zero_le (B^4),Nat.zero_le (B^5),Nat.zero_le (B^6)]
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.HeadGate

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.StagedGate
open OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram

theorem bodyPolynomial_le (B : ℕ) : bodyPolynomial B≤16000*(B+1)^6 := by
  have hg := HeadGate.gatePolynomial_le B
  dsimp [bodyPolynomial]
  nlinarith only [hg,Nat.zero_le B,Nat.zero_le (B^2),Nat.zero_le (B^3),
    Nat.zero_le (B^4),Nat.zero_le (B^5),Nat.zero_le (B^6)]
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.StagedGate
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadAcceptedCorrect
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The fixed accepted branch physically overlays the current assignment,
computes its whole specialized factor product, and adds that same dictionary
to the head sum. Its compact return cap is independent of its transient cost. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedCorrect

open OAI BitProgram StructuredCalls SubexpSetupStorage
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram MomentsProgram
open OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open FactorAssignmentProgram FactorAssignmentBoundary QueryTupleState
open HighQueryAdapter TruncatedRingProgram

noncomputable section
attribute [local simp] Fin.coe_ofNat_eq_mod

/-- The concrete accepted command has a fixed polynomial cost in its physical
boundary and the actual uniform factor-callback budget. The exponent is
independent of all runtime dimensions. -/
theorem budget_polynomial {r Q n d : ℕ} (q : Factor.Spec r Q n d) (P S Z : ℕ) :
    budget q P S Z ≤ 3020000 *
      (entryScratch.length + n + baseWidth 3 q.p.t + d + q.u + q.J + P +
        FactorAssignmentCallback.uniformCallbackBudget q P S Z + 1)^10 := by
  let X := entryScratch.length + n + baseWidth 3 q.p.t + d + q.u + q.J + P +
    FactorAssignmentCallback.uniformCallbackBudget q P S Z + 1
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hP : P ≤ X := by dsimp [X]; omega
  have h0 : 1 ≤ X^10 := Nat.one_le_pow _ _ hX
  have h1 : X ≤ X^10 := by
    simpa using Nat.pow_le_pow_right hX (show 1 ≤ 10 by decide)
  have h4 : X^4 ≤ X^10 := Nat.pow_le_pow_right hX (by decide)
  have ha := FactorAssignmentCorrect.assignmentBudget_polynomial q P S Z
  change FactorAssignmentCorrect.assignmentBudget q P S Z ≤ 1600 * X^4 at ha
  have hd : n + baseWidth 3 q.p.t + d + q.u + q.J + 1 ≤ X := by dsimp [X]; omega
  have hb := (additionBudget_le_local n (baseWidth 3 q.p.t) d q.u q.J 0).trans
    (localBudget_le n (baseWidth 3 q.p.t) d q.u q.J 0)
  simp only [Nat.add_zero] at hb
  have hc : additionBudget n (baseWidth 3 q.p.t) d q.u q.J ≤ 3000000 * X^10 := by
    apply hb.trans
    gcongr
  change 70*P+70 + FactorAssignmentCorrect.assignmentBudget q P S Z +
    additionBudget n (baseWidth 3 q.p.t) d q.u q.J + 14*(896*P)+22 ≤ 3020000*X^10
  omega

/-- One input-polynomial envelope covers the compact boundary, actual gate,
and concrete accepted branch. It may be fixed once for every head iteration. -/
theorem body_envelope_polynomial {r Q n d : ℕ} (q : Factor.Spec r Q n d) (P S Z : ℕ) :
    896*P + HeadEvaluationProgram.StagedGate.bodyPolynomial P + budget q P S Z ≤
      3040000 * (entryScratch.length + n + baseWidth 3 q.p.t + d + q.u + q.J + P +
        FactorAssignmentCallback.uniformCallbackBudget q P S Z + 1)^10 := by
  let X := entryScratch.length + n + baseWidth 3 q.p.t + d + q.u + q.J + P +
    FactorAssignmentCallback.uniformCallbackBudget q P S Z + 1
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hP : P+1 ≤ X := by dsimp [X]; omega
  have h1 : X ≤ X^10 := by
    simpa using Nat.pow_le_pow_right hX (show 1 ≤ 10 by decide)
  have h6 : X^6 ≤ X^10 := Nat.pow_le_pow_right hX (by decide)
  have hg : HeadEvaluationProgram.StagedGate.bodyPolynomial P ≤ 16000*X^6 := by
    apply (HeadEvaluationProgram.StagedGate.bodyPolynomial_le P).trans
    gcongr
  have ha := budget_polynomial q P S Z
  change budget q P S Z ≤ 3020000*X^10 at ha
  change 896*P + HeadEvaluationProgram.StagedGate.bodyPolynomial P + budget q P S Z ≤
    3040000*X^10
  omega

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedCorrect
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadSumBudgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Explicit compact boundary, source and arithmetic caps for the actual head
sum. Their fixed polynomial certificates depend on source dimensions and
physical word lengths, independently of the number of head assignments. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumBudgets
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram OAI.Algorithms.SubexponentialSAT.SubexpLiftRing
open OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.Polynomial
open FactorTableBudgets

private theorem table_scalar_caps (A : ℕ) :
    A ≤ tableScalarCap A ∧ sourceCap A ≤ tableScalarCap A ∧
    1029*compactCap A+99 ≤ tableScalarCap A ∧ compactCap A ≤ tableScalarCap A := by
  unfold tableScalarCap
  omega

theorem table_budget_le {r Q n d : ℕ} (q : Factor.Spec r Q n d) (A : ℕ)
    (hr : r ≤ A) (hQ : Q ≤ A) (hd : d ≤ A) (hn : n ≤ A)
    (ht : q.p.t ≤ A) (hR : q.p.R ≤ A) (hu : q.u ≤ A) (hJ : q.J ≤ A)
    (ha : q.p.aWord.length ≤ A) (hw : q.p.width.length ≤ A)
    (hp : RowSelectionProgram.pairLength q.p.power ≤ A) :
    FactorAssignmentCallback.tableBudget q (compactCap A) (sourceCap A) ≤
      tableEnvelope (tableScalarCap A) := by
  obtain ⟨hA,hS,hH,hP⟩ := table_scalar_caps A
  have hl := literal_work_le q.p q.u q.J n (sourceCap A) (1029*compactCap A+99)
    (tableScalarCap A) (hu.trans hA) (hJ.trans hA) (hn.trans hA) hS hH
    (hr.trans hA) (hQ.trans hA) (hd.trans hA) (ht.trans hA) (hR.trans hA)
    (ha.trans hA) (hw.trans hA) (hp.trans hA)
  have hb := payload_bound_le n q.u q.J q.p.t d (tableScalarCap A)
    (hn.trans hA) (hu.trans hA) (hJ.trans hA) (ht.trans hA) (hd.trans hA)
  have hn' := hn.trans hA
  unfold FactorAssignmentCallback.tableBudget tableEnvelope
  gcongr

theorem callback_budget_le {r Q n d : ℕ} (q : Factor.Spec r Q n d) (A : ℕ)
    (hr : r ≤ A) (hQ : Q ≤ A) (hd : d ≤ A) (hn : n ≤ A)
    (ht : q.p.t ≤ A) (hR : q.p.R ≤ A) (hu : q.u ≤ A) (hJ : q.J ≤ A)
    (ha : q.p.aWord.length ≤ A) (hw : q.p.width.length ≤ A)
    (hp : RowSelectionProgram.pairLength q.p.power ≤ A) :
    FactorAssignmentCallback.uniformCallbackBudget q (compactCap A) (sourceCap A)
      (arithmeticCap A) ≤ callbackEnvelope A := by
  have hb := table_budget_le q A hr hQ hd hn ht hR hu hJ ha hw hp
  unfold FactorAssignmentCallback.uniformCallbackBudget callbackEnvelope
  omega

theorem body_budget_le {r Q n d : ℕ} (q : Factor.Spec r Q n d) (A : ℕ)
    (hr : r ≤ A) (hQ : Q ≤ A) (hd : d ≤ A) (hn : n ≤ A)
    (ht : q.p.t ≤ A) (hR : q.p.R ≤ A) (hu : q.u ≤ A) (hJ : q.J ≤ A)
    (ha : q.p.aWord.length ≤ A) (hw : q.p.width.length ≤ A)
    (hp : RowSelectionProgram.pairLength q.p.power ≤ A) :
    896*compactCap A+HeadEvaluationProgram.StagedGate.bodyPolynomial (compactCap A)+
      HeadAcceptedCorrect.budget q (compactCap A) (sourceCap A) (arithmeticCap A) ≤
        bodyEnvelope A := by
  apply (HeadAcceptedCorrect.body_envelope_polynomial q (compactCap A) (sourceCap A)
    (arithmeticCap A)).trans
  have hc := callback_budget_le q A hr hQ hd hn ht hR hu hJ ha hw hp
  unfold bodyEnvelope
  simp only [RingProgram.ternary_baseWidth]
  gcongr

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumBudgets
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_NodeTimeColumns
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.NodeTime
open SubexponentialSAT Subexp SubexpLiftRing SubexpSetupStorage
open LeafHeadSetupProgram LeafHeadSetupProgram.Bounds
open LayoutProgram RowSelectionProgram

theorem inputBounds (s : Native.Inputs) (a : LeafHeadSetupProgram.Data)
    (h : Native.Ready s a) (B : ℕ) (hb : WordBound B a) : InputBounds s B := by
  have hp : (LayoutOwnerFiberProgram.stream s.plans).length ≤ B := by simpa only [h.plans] using hb 136
  have hc := Encoding.length_encodeList_lower (fun p : ℕ×ℕ => LayoutOwnerFiberProgram.pairPayload p.1 p.2) s.plans
  have hd : s.D ≤ B := by
    change s.plans.length+1 ≤ (LayoutOwnerFiberProgram.stream s.plans).length at hc
    rw [s.plans_length] at hc
    omega
  exact ⟨by simpa [h.ambient,unary] using hb 128,hd,
    by simpa [h.colors,unary] using hb 130,by simpa [h.nodes,unary] using hb 131,
    by simpa [h.order,unary] using hb 138,by simpa only [h.width] using hb 140,
    by simpa only [h.height] using hb 139,by simpa only [h.metadata] using hb 135,hp,
    by simpa [h.wordWidth,unary] using hb 132⟩

end SubexponentialSAT.SqrtLog.NodeTime

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryHeadBudgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! A concrete numerical HeadBounds certificate for the actual visitor.
Source columns are bounded from its stored native input, all incidence rows
remain present, and the compact endpoint cap is separate from transient space. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadBudgets
open OAI BitProgram StructuredCalls SubexpSetupStorage SubexpLiftRing
open SqrtLog SqrtLog.LeafProgram SqrtLog.LeafHeadSetupProgram
open HeadSumBudgets FactorTableBudgets
open OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.Polynomial

private theorem sourceSize_large (A : ℕ) : A+1 ≤ sourceSize A := by
  unfold sourceSize
  omega

private theorem scalarCap_large (A : ℕ) : sourceSize A+1 ≤ scalarCap A := by
  have h : sourceSize A+1 ≤ (sourceSize A+1)^10 := Nat.le_self_pow (by decide) _
  unfold scalarCap
  omega

theorem original_le_scalar (A : ℕ) : A+1 ≤ scalarCap A := by
  have h1 := sourceSize_large A
  have h2 := scalarCap_large A
  omega

theorem multiply_budget_le {r Q n d : ℕ} (q : Factor.Spec r Q n d) (A : ℕ)
    (hn : n ≤ A) (hd : d ≤ A) (ht : q.p.t ≤ A) (hJ : q.J ≤ A) :
    QueryVisitorHead.multiplyBudget q (compact A) ≤ multiplyEnvelope A := by
  have h := FactorProductSpace.budget_polynomial n (baseWidth 3 q.p.t) d q.p.t q.J
  have hscale : n+baseWidth 3 q.p.t+d+q.p.t+q.J+1 ≤ 6*A+1 := by
    simp only [RingProgram.ternary_baseWidth]
    omega
  unfold QueryVisitorHead.multiplyBudget multiplyEnvelope
  gcongr
  exact h.trans (by gcongr)

theorem visitor_time_coefficient_le {r Q n d : ℕ} (q : Factor.Spec r Q n d) (A : ℕ)
    (hr : r ≤ A) (hQ : Q ≤ A) (hn : n ≤ A) (hd : d ≤ A)
    (ht : q.p.t ≤ A) (hR : q.p.R ≤ A) (hu : q.u ≤ A) (hJ : q.J ≤ A)
    (hw : q.p.width.length ≤ A) (hp : RowSelectionProgram.pairLength q.p.power ≤ A+1) :
    QueryVisitorHead.timeCoefficient q A (compact A) (source A) (arithmetic A)
      (transient A) ≤ visitorEnvelope A := by
  let T := scalarCap A
  have hAT := original_le_scalar A
  have hA : A ≤ T := by dsimp [T]; omega
  have hs := HeadSumBudgets.body_budget_le q T (hr.trans hA) (hQ.trans hA)
    (hd.trans hA) (hn.trans hA) (ht.trans hA) (hR.trans hA) (hu.trans hA) (hJ.trans hA)
    (q.p.hAQ.trans (hQ.trans hA)) (hw.trans hA) (hp.trans hAT)
  have hm := multiply_budget_le q A hn hd ht hJ
  have hn' := hn.trans hA
  unfold QueryVisitorHead.timeCoefficient visitorEnvelope HeadSumBudgets.iterationEnvelope
  change QueryVisitorLoad.runEnvelope A (compact A)+100*compact A+200+
    (2*(HeadEvaluationProgram.StagedGate.bodyPolynomial (compactCap T)+
      HeadAcceptedCorrect.budget q (compactCap T) (sourceCap T) (arithmeticCap T))+
      126*prefixCap T+54*n+286)+QueryVisitorHead.multiplyBudget q (compact A) ≤
    QueryVisitorLoad.runEnvelope A (compact A)+100*compact A+200+
      (2*bodyEnvelope T+126*prefixCap T+54*T+286)+multiplyEnvelope A+
      996*compact A+200+transient A+896*compact A
  omega

theorem visitor_prefix_le {r Q n d : ℕ} (q : Factor.Spec r Q n d) (A : ℕ)
    (hn : n ≤ A) (hd : d ≤ A) (ht : q.p.t ≤ A) (hJ : q.J ≤ A) :
    max (QueryVisitorLoad.runEnvelope A (compact A))
      (max (996*compact A+200)
        (max (transient A) (896*compact A+QueryVisitorHead.multiplyBudget q (compact A)))) ≤
      visitorEnvelope A := by
  have hm := multiply_budget_le q A hn hd ht hJ
  unfold visitorEnvelope
  exact max_le (by omega) (max_le (by omega) (max_le (by omega) (by omega)))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadBudgets
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryVisitorSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete execution of the two representative passes. The saved frame
stack is traversed in place, and every semantic dictionary is the one written
by the actual arithmetic command. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open SubexpSetupStorage LeafHeadSetupProgram
open SubexpLiftRing SubexpQuarticRing MomentsProgram TruncatedRingProgram
open QueryTupleState QueryTupleVisitor SignatureTupleProgram SignatureTupleSource


open scoped BigOperators

theorem visitorCost_le (s : ProducedSource) {d : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d)
    (P S Z B height : ℕ) :
    visitorCost s q P S Z B height ≤
      visitorCoefficient s q P S Z B*(s.input.r+1)*2^height := by
  have hp : 1 ≤ 2^height := one_le_pow₀ (by omega)
  let c := visitorCoefficient s q P S Z B
  have hbase : QueryTupleSum.budget s.input.n (baseWidth 3 q.p.t) d q.p.t q.J P+
      1600*(P+1) ≤ c*2^height := by
    calc
      _ ≤ c := by dsimp [c,visitorCoefficient];omega
      _ ≤ c*2^height := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left c hp
  have hhead : baselineCost s P+evaluationCost s q P S Z B height+20 ≤ c*2^height := by
    unfold evaluationCost
    calc
      _ ≤ (baselineCost s P+QueryVisitorHead.timeCoefficient q s.bound P S Z B+20)*2^height := by
        nlinarith
      _ ≤ c*2^height := Nat.mul_le_mul_right _ (by dsimp [c,visitorCoefficient];omega)
  calc
    visitorCost s q P S Z B height ≤ c*2^height+(c*2^height)*s.input.r :=
      Nat.add_le_add hbase (Nat.mul_le_mul_right _ hhead)
    _ = visitorCoefficient s q P S Z B*(s.input.r+1)*2^height := by dsimp [c];ring

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryVisitorBudgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Polynomial overhead and prefix space for the complete actual tuple
visitor. The number of heads and the proved maximum head-size exponent stay
explicit; the empty-head/empty-tuple term is retained. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorBudgets
open OAI SqrtLog SubexpLiftRing SubexpSetupStorage
open SignatureTupleSource LeafHeadSetupProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.Polynomial

theorem tail_le {r Q n d : ℕ} (q : LeafProgram.Factor.Spec r Q n d) (A : ℕ)
    (hn : n ≤ A) (hd : d ≤ A) (ht : q.p.t ≤ A) (hJ : q.J ≤ A) :
    QueryTupleSum.budget n (baseWidth 3 q.p.t) d q.p.t q.J (QueryHeadBudgets.compact A) ≤
      tailEnvelope A := by
  apply (QueryTupleSum.budget_polynomial n (baseWidth 3 q.p.t) d q.p.t q.J
    (QueryHeadBudgets.compact A)).trans
  unfold tailEnvelope
  simp only [RingProgram.ternary_baseWidth]
  gcongr
  omega

private theorem baseline_le (s : ProducedSource) (A : ℕ) (hs : s.bound ≤ A) :
    QueryVisitorSemantics.baselineCost s (QueryHeadBudgets.compact A) ≤ baselineEnvelope A := by
  unfold QueryVisitorSemantics.baselineCost baselineEnvelope QueryVisitorLoad.runEnvelope
  gcongr

/-- The actual source words, rather than their exponential integer values,
supply every remaining local head coefficient parameter. -/
theorem head_coefficient_le (s : ProducedSource) {d : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d) (A : ℕ)
    (hs : s.bound ≤ A) (hd : d ≤ A) (ht : q.p.t ≤ A) (hu : q.u ≤ A) (hJ : q.J ≤ A)
    (hR : q.p.R = s.input.R) (hw : q.p.width = s.input.width)
    (hp : q.p.power = s.input.power) :
    QueryVisitorHead.timeCoefficient q s.bound (QueryHeadBudgets.compact A)
      (QueryHeadBudgets.source A) (QueryHeadBudgets.arithmetic A) (QueryHeadBudgets.transient A) ≤
        QueryHeadBudgets.visitorEnvelope A := by
  have hi := NodeTime.inputBounds s.input s.source s.ready s.bound s.bounded
  have hpower : RowSelectionProgram.pairLength q.p.power ≤ A+1 := by
    rw [hp]
    simp only [RowSelectionProgram.pairLength,Native.Inputs.power,
      LayoutProgram.IntegerCache.denominatorWord,List.length_append,List.length_replicate,
      List.length_singleton,List.length_nil,Nat.add_zero]
    have := hi.R
    omega
  have hR' : q.p.R ≤ A := hR ▸ hi.R.trans hs
  have hw' : q.p.width.length ≤ A := hw ▸ hi.width.trans hs
  have hhead := QueryHeadBudgets.visitor_time_coefficient_le q A
    (hi.r.trans hs) (hi.Q.trans hs) (hi.n.trans hs) hd ht hR' hu hJ hw' hpower
  apply le_trans (b := QueryVisitorHead.timeCoefficient q A (QueryHeadBudgets.compact A)
    (QueryHeadBudgets.source A) (QueryHeadBudgets.arithmetic A) (QueryHeadBudgets.transient A)) ?_ hhead
  unfold QueryVisitorHead.timeCoefficient QueryVisitorLoad.runEnvelope
  gcongr

/-- Both measured quantities are the ones returned by the actual visitor
run theorem. Neither side grows with the number of emitted tuples. -/
theorem actual_bounds (s : ProducedSource) {d : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d) (A : ℕ)
    (hs : s.bound ≤ A) (hd : d ≤ A) (ht : q.p.t ≤ A) (hu : q.u ≤ A) (hJ : q.J ≤ A)
    (hR : q.p.R = s.input.R) (hw : q.p.width = s.input.width)
    (hp : q.p.power = s.input.power) :
    QueryVisitorSemantics.visitorCoefficient s q (QueryHeadBudgets.compact A)
      (QueryHeadBudgets.source A) (QueryHeadBudgets.arithmetic A) (QueryHeadBudgets.transient A) ≤
        envelope A ∧
    QueryVisitorSemantics.visitorSpace s q (QueryHeadBudgets.compact A)
      (QueryHeadBudgets.transient A) ≤ envelope A := by
  have hi := NodeTime.inputBounds s.input s.source s.ready s.bound s.bounded
  have hn := hi.n.trans hs
  have htail := tail_le q A hn hd ht hJ
  have hbase := baseline_le s A hs
  have hhead := head_coefficient_le s q A hs hd ht hu hJ hR hw hp
  have hprefix := QueryHeadBudgets.visitor_prefix_le q A hn hd ht hJ
  have heval : QueryVisitorSemantics.evaluationSpace s q (QueryHeadBudgets.compact A)
      (QueryHeadBudgets.transient A) ≤ QueryHeadBudgets.visitorEnvelope A := by
    apply le_trans (b := max (QueryVisitorLoad.runEnvelope A (QueryHeadBudgets.compact A))
      (max (996*QueryHeadBudgets.compact A+200)
        (max (QueryHeadBudgets.transient A)
          (896*QueryHeadBudgets.compact A+QueryVisitorHead.multiplyBudget q (QueryHeadBudgets.compact A))))) ?_ hprefix
    unfold QueryVisitorSemantics.evaluationSpace QueryVisitorLoad.runEnvelope
    gcongr
  constructor
  · unfold QueryVisitorSemantics.visitorCoefficient envelope
    omega
  · unfold QueryVisitorSemantics.visitorSpace envelope
    exact max_le (by omega) (by omega)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorBudgets
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleComplete
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete cursor invariants for the fixed attained-signature controller.
The integer head matrices come from native source words.  Each boundary uses
one retained cap; reload and predecessor-scan prefix bounds remain transient.
-/

noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete

open Classical
open OAI.Algorithms.SubexponentialSAT.SubexpLiftRing
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open LeafHeadSetupProgram OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage
open SignatureTupleDFS SignatureTupleTraversal SignatureTupleProgram
open SignatureTupleNative SignatureTupleRefinement SignatureTupleLoader SignatureTupleSource

theorem prefix_count_positive (h : ℕ → ℕ) {κ : ℕ → Type*}
    (key : (d : ℕ) → Fin (2^h d) → κ d) (levels : ℕ) :
    1 ≤ prefixCount (fun d => Fintype.card (Representatives key d)) levels := by
  classical
  have hp (d : ℕ) : 1 ≤ Fintype.card (Representatives key d) := by
    have hn : 0 < Fintype.card (Representatives key d) := by
      simpa only [Nat.card_eq_fintype_card] using
        AttainedSignatures.card_representative_pos (key d)
          (pow_pos (by decide : 0 < (2 : ℕ)) _)
    omega
  simpa only [prefixCount_zero] using
    prefixCount_le (fun d => Fintype.card (Representatives key d)) (Nat.zero_le levels)
      (fun d _ => hp d)


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_TupleRunBudgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The same compact endpoint cap supports the actual tuple controller and
its visitor. Transient scanner/reload work is bounded separately; none of it
is fed back into the retained frame cap between pairs. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TupleRunBudgets
open OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.Polynomial
open SignatureTupleSource SignatureTupleComplete SignatureTupleLoader

theorem event_bounds (s : ProducedSource) (A : ℕ) (hs : s.bound ≤ A) :
    eventPolynomial s (QueryHeadBudgets.compact A) ≤ eventEnvelope A ∧
    prefixEnvelope s (QueryHeadBudgets.compact A) ≤ eventEnvelope A ∧
    QueryHeadBudgets.compact A ≤ eventEnvelope A := by
  have hscan : scannerEnvelope s.bound ≤ scannerEnvelope A := by
    unfold scannerEnvelope
    gcongr
  have hrun : SignatureTupleLoader.runEnvelope s.bound (QueryHeadBudgets.compact A) ≤
      SignatureTupleLoader.runEnvelope A (QueryHeadBudgets.compact A) := by
    unfold SignatureTupleLoader.runEnvelope
    gcongr
  unfold eventPolynomial prefixEnvelope eventEnvelope
  exact ⟨by omega,by omega,by omega⟩

private theorem time_bound (P C r K H V : ℕ) (hP : P ≤ C) (hK : 1 ≤ K)
    (hV : V ≤ C*(r+1)*2^H) :
    P+(2*P)*r*K*4^H+K*(V+P)+2 ≤ (5*C+2)*(r+1)*K*4^H := by
  have h4 : 1 ≤ 4^H := one_le_pow₀ (by decide)
  have hpower : 2^H ≤ 4^H := Nat.pow_le_pow_left (by decide) H
  have hR : 1 ≤ (r+1)*K*4^H := by
    simpa only [one_mul] using Nat.mul_le_mul
      (Nat.mul_le_mul (show 1 ≤ r+1 by omega) hK) h4
  have hfirst : P ≤ C*(r+1)*K*4^H := by
    calc
      P ≤ C := hP
      _ = C*1 := (Nat.mul_one _).symm
      _ ≤ C*((r+1)*K*4^H) := Nat.mul_le_mul_left C hR
      _ = _ := by ring
  have hscan : (2*P)*r*K*4^H ≤ (2*C)*(r+1)*K*4^H := by gcongr; omega
  have hvisit : K*V ≤ C*(r+1)*K*4^H := by
    calc
      K*V ≤ K*(C*(r+1)*2^H) := Nat.mul_le_mul_left K hV
      _ ≤ K*(C*(r+1)*4^H) := by gcongr
      _ = _ := by ring
  have hreturn : K*P ≤ C*(r+1)*K*4^H := by
    calc
      K*P ≤ K*C := Nat.mul_le_mul_left K hP
      _ = C*1*K*1 := by ring
      _ ≤ C*(r+1)*K*4^H := by gcongr; omega
  have hfinal : 2 ≤ 2*(r+1)*K*4^H := by
    simpa only [Nat.mul_one,Nat.mul_assoc] using Nat.mul_le_mul_left 2 hR
  calc
    P+(2*P)*r*K*4^H+K*(V+P)+2 ≤
        C*(r+1)*K*4^H+(2*C)*(r+1)*K*4^H+
        (C*(r+1)*K*4^H+C*(r+1)*K*4^H)+2*(r+1)*K*4^H := by
      rw [Nat.mul_add]
      omega
    _ = _ := by ring

/-- Both bounds name the measured quantities of the actual unified native
run, with the unique empty tuple and all losing scans included. -/
theorem run_bounds_oai (s : ProducedSource) {d : ℕ}
    (q : OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d) (A : ℕ)
    (hs : s.bound ≤ A) (hd : d ≤ A) (ht : q.p.t ≤ A) (hu : q.u ≤ A) (hJ : q.J ≤ A)
    (hR : q.p.R = s.input.R) (hw : q.p.width = s.input.width)
    (hp : q.p.power = s.input.power) :
    SignatureTupleRun.completeSpace s q (QueryHeadBudgets.compact A)
      (QueryHeadBudgets.transient A) ≤ runCoefficient A ∧
    ∀ height, SignatureTupleRun.runTime s q (QueryHeadBudgets.compact A)
      (QueryHeadBudgets.source A) (QueryHeadBudgets.arithmetic A)
      (QueryHeadBudgets.transient A) height ≤
      runCoefficient A*(s.input.r+1)*SignatureTupleRun.tupleCount s.key s.input.r*4^height := by
  have hevent := event_bounds s A hs
  obtain ⟨hvisitor,hspace⟩ := QueryVisitorBudgets.actual_bounds s q A hs hd ht hu hJ hR hw hp
  have hi := OAI.Algorithms.SubexponentialSAT.SqrtLog.NodeTime.inputBounds s.input s.source s.ready s.bound s.bounded
  have htail := QueryVisitorBudgets.tail_le q A (hi.n.trans hs) hd ht hJ
  have hP : eventPolynomial s (QueryHeadBudgets.compact A) ≤ envelope A := by
    unfold envelope
    omega
  constructor
  · unfold SignatureTupleRun.completeSpace SignatureTupleRun.runSpace runCoefficient envelope
    apply max_le
    · exact max_le (by omega) (by omega)
    · omega
  · intro height
    have hV := QueryVisitorSemantics.visitorCost_le s q (QueryHeadBudgets.compact A)
      (QueryHeadBudgets.source A) (QueryHeadBudgets.arithmetic A)
      (QueryHeadBudgets.transient A) height
    have hv : QueryVisitorSemantics.visitorCost s q (QueryHeadBudgets.compact A)
        (QueryHeadBudgets.source A) (QueryHeadBudgets.arithmetic A)
        (QueryHeadBudgets.transient A) height ≤ envelope A*(s.input.r+1)*2^height := by
      apply hV.trans
      gcongr
      unfold envelope
      omega
    have hk : 1 ≤ SignatureTupleRun.tupleCount s.key s.input.r := by
      exact prefix_count_positive s.headSize s.key s.input.r
    apply (time_bound _ _ _ _ _ _ hP hk hv).trans
    have hcoeff : 5*envelope A+2 ≤ runCoefficient A := by
      unfold runCoefficient
      omega
    exact Nat.mul_le_mul_right (4^height) (Nat.mul_le_mul_right
      (SignatureTupleRun.tupleCount s.key s.input.r) (Nat.mul_le_mul_right (s.input.r+1) hcoeff))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TupleRunBudgets
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TupleRunBudgets.run_bounds_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TupleRunBudgets.run_bounds_oai
