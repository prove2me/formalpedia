-- Prove2me | solution 1 for HILL.PRG.false_entropy_to_pseudoentropy_with_gap
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-18T06:59:37.53794+00:00
-- url     : https://prove2.me/submissions/60ed1103-ce11-4840-9993-39c0c8f7a32d

import Definitions.Def_HILL_PRG_Model
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Definitions.Def_PricingWithTips3DM_0b2f8d1d07e5b5a6b6ac84b8
import Definitions.Def_PricingWithTips3DM_693ce23dec6dc45ed34c4fb1
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.FinRange
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Tauto
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.List.Induction
import Mathlib.Data.List.TakeDrop
import Definitions.Def_PricingWithTips3DM_d8886977e67d59ff4f35de9d
import Definitions.Def_PricingWithTips3DM_3799fd79c9b0b4d68c438353
import Definitions.Def_PricingWithTips3DM_4901b5edb9039a7b71dab674
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

section HILL416_Contracts

/-!
# HILL Lemma 4.16: proposed proof interfaces

Target: https://prove2.me/theorems/d8efa933-270e-4991-8fec-d6e8958fd1bc
Model: https://prove2.me/theorems/fd67e56c-b9cc-4f86-987d-d1c6d884b1f1
Environment: Lean v4.33.1; Mathlib 0df444a.

This file is NOT a proof of the target theorem. Declarations named Contract or
Statement define propositions to prove; they do not assert those propositions.
No extraction theorem or polynomial-time machine certificate is assumed as an
axiom. The final section contains only elementary consequences of explicit
interface hypotheses.

Validation: all declarations and the five InterfaceConsequences proof bodies
elaborated successfully with Lean v4.33.1 and Mathlib 0df444a in a local
reduced-import harness. That harness preserved every HILL and Levin declaration
and body, replacing only their broad `import Mathlib` lines with focused imports
from the same Mathlib revision. This deliverable retains its original
`import Definitions.Def_HILL_PRG_Model` line. The full original-import Prove2Me
environment was not built or submitted for verification.

The five proved consequences were audited with `#print axioms`; each depends
only on `propext`, `Classical.choice`, and `Quot.sound`. Their explicit contract
hypotheses remain theorem parameters, not proved facts. The remaining contract
propositions are unproved.

Recommended work order:
1. Flat leftover hashing and finite counting/entropy identities.
2. Finite iid concentration, using Mathlib's SubGaussian theorems.
3. Concrete TM2 composition, encoded-word batch calls, parsing and hashing.
4. Coin-length advice simulation and the single-adversary product hybrid.
5. The padded construction and entropy-witness assembly.
-/

/-
Research contract definitions for the HILL model.
These are proposed theorem STATEMENTS, encoded as Prop-valued definitions.
Only the final InterfaceConsequences section contains proof bodies. The
contract propositions themselves remain unproved; see the validation status
above for the scope of compilation checks.
-/

namespace HILL.PRG.Proposed

open HILL.PRG

section FiniteHashing

variable {α β κ ζ : Type*}
variable [DecidableEq α] [DecidableEq β] [DecidableEq κ] [DecidableEq ζ]

def fiberCardOn (S : Finset α) (f : α → β) (y : β) : ℕ :=
  (S.filter (fun x => f x = y)).card

noncomputable def smallFiberProb
    (S : Finset α) (f : α → β) (L : ℝ) : ℝ := by
  classical
  exact uniformProb S (fun x => (fiberCardOn S f (f x) : ℝ) < L)

def CollisionUniversalOn
    (S : Finset α) (R : Finset κ) (Z : Finset ζ)
    (h : κ → α → ζ) : Prop :=
  ∀ x ∈ S, ∀ x' ∈ S, x ≠ x' →
    (Z.card : ℝ) * ((R.filter (fun r => h r x = h r x')).card : ℝ)
      ≤ (R.card : ℝ)

def hashSupportOn
    (S : Finset α) (R : Finset κ) (Z : Finset ζ)
    (f : α → β) : Finset (β × (κ × ζ)) :=
  (S.image f) ×ˢ (R ×ˢ Z)

noncomputable def hashActualOn
    (S : Finset α) (R : Finset κ)
    (f : α → β) (h : κ → α → ζ) : β × (κ × ζ) → ℝ :=
  lawOn (S ×ˢ R) (fun xr => (f xr.1, (xr.2, h xr.2 xr.1)))

noncomputable def hashIdealOn
    (S : Finset α) (R : Finset κ) (Z : Finset ζ)
    (f : α → β) : β × (κ × ζ) → ℝ :=
  lawOn ((S ×ˢ R) ×ˢ Z)
    (fun xrz => (f xrz.1.1, (xrz.1.2, xrz.2)))

def FlatLeftoverHashStatement : Prop :=
  ∀ (S : Finset α) (R : Finset κ) (Z : Finset ζ) (h : κ → α → ζ),
    S.Nonempty → R.Nonempty → Z.Nonempty →
    (∀ r ∈ R, ∀ x ∈ S, h r x ∈ Z) →
    CollisionUniversalOn S R Z h →
    statDistOn (R ×ˢ Z)
      (lawOn (S ×ˢ R) (fun xr => (xr.2, h xr.2 xr.1)))
      (lawOn (R ×ˢ Z) id)
      ≤ (1 / 2 : ℝ) * Real.sqrt ((Z.card : ℝ) / (S.card : ℝ))

def FlatConditionalHashStatement : Prop :=
  ∀ (S : Finset α) (R : Finset κ) (Z : Finset ζ)
    (f : α → β) (h : κ → α → ζ),
    S.Nonempty → R.Nonempty → Z.Nonempty →
    (∀ r ∈ R, ∀ x ∈ S, h r x ∈ Z) →
    CollisionUniversalOn S R Z h →
    ∀ L : ℝ, 0 < L →
    statDistOn (hashSupportOn S R Z f)
      (hashActualOn S R f h) (hashIdealOn S R Z f)
      ≤ smallFiberProb S f L +
        (1 / 2 : ℝ) * Real.sqrt ((Z.card : ℝ) / L)

def FlatConditionalHashBitsStatement : Prop :=
  ∀ (S : Finset α) (R : Finset κ) (Z : Finset ζ)
    (f : α → β) (h : κ → α → ζ),
    S.Nonempty → R.Nonempty → Z.Nonempty →
    (∀ r ∈ R, ∀ x ∈ S, h r x ∈ Z) →
    CollisionUniversalOn S R Z h →
    ∀ j m : ℕ, Z.card = 2 ^ j →
    ∀ δ : ℝ, smallFiberProb S f ((2 : ℝ) ^ (j + 2 * m)) ≤ δ →
    statDistOn (hashSupportOn S R Z f)
      (hashActualOn S R f h) (hashIdealOn S R Z f)
      ≤ δ + 1 / (2 : ℝ) ^ (m + 1)

noncomputable def averageOn (S : Finset α) (W : α → ℝ) : ℝ :=
  (∑ x ∈ S, W x) / (S.card : ℝ)

noncomputable def logFiberOn (S : Finset α) (f : α → β) (x : α) : ℝ :=
  Real.logb 2 (fiberCardOn S f (f x) : ℝ)

def MeanLogFiberStatement : Prop :=
  ∀ (S : Finset α) (f : α → β), S.Nonempty →
    averageOn S (logFiberOn S f) =
      Real.logb 2 (S.card : ℝ) - entropyOf S f

def LogFiberBoundsStatement : Prop :=
  ∀ (S : Finset α) (f : α → β), ∀ x ∈ S,
    0 ≤ logFiberOn S f x ∧
      logFiberOn S f x ≤ Real.logb 2 (S.card : ℝ)

def EntropyOfOnSupersetStatement : Prop :=
  ∀ (S : Finset α) (B : Finset β) (f : α → β),
    (∀ x ∈ S, f x ∈ B) →
    entropyOf S f = shannonOn B (lawOn S f)

def ProductFiberStatement : Prop :=
  ∀ (S : Finset α) (f : α → β) (k : ℕ) (ys : Fin k → β),
    fiberCardOn (Fintype.piFinset (fun _ : Fin k => S))
      (fun xs i => f (xs i)) ys =
        ∏ i : Fin k, fiberCardOn S f (ys i)

def ProductEntropyStatement : Prop :=
  ∀ (S : Finset α) (f : α → β), S.Nonempty → ∀ k : ℕ,
    entropyOf (Fintype.piFinset (fun _ : Fin k => S))
      (fun xs i => f (xs i)) = (k : ℝ) * entropyOf S f

def EntropyInjectiveMapStatement : Prop :=
  ∀ (S : Finset α) (f : α → β) (g : β → ζ),
    Set.InjOn g (S.image f : Set β) →
    entropyOf S (g ∘ f) = entropyOf S f

noncomputable def iidLowerTailOn
    (S : Finset α) (W : α → ℝ) (k : ℕ) (r : ℝ) : ℝ := by
  classical
  exact uniformProb (Fintype.piFinset (fun _ : Fin k => S))
    (fun xs => (∑ i : Fin k, W (xs i)) < r)

def FiniteIIDLowerTailStatement : Prop :=
  ∀ (S : Finset α) (W : α → ℝ), S.Nonempty →
    ∀ B η : ℝ, 0 < B → 0 ≤ η →
    (∀ x ∈ S, 0 ≤ W x ∧ W x ≤ B) →
    ∀ k : ℕ, 0 < k →
    iidLowerTailOn S W k ((k : ℝ) * (averageOn S W - η))
      ≤ Real.exp (-(2 * (k : ℝ) * η ^ 2) / B ^ 2)

def repeatEval {k : ℕ} (f : α → β) (xs : Fin k → α) : Fin k → β :=
  fun i => f (xs i)

/-- Applies to a universal hash on repeated seeds; affine universality is a separate proof. -/
def RepeatedUniformExtractionStatement : Prop :=
  ∀ (T k j m : ℕ) (f : Bits → Bits) (R : Finset κ)
    (h : κ → (Fin k → Bits) → Bits) (s : ℝ),
    0 < k → R.Nonempty → 0 < s →
    j = Nat.floor ((k : ℝ) *
      ((T : ℝ) - entropyOf (cube T) f - s / 2)) →
    2 * (m : ℝ) ≤ (k : ℝ) * s / 4 →
    let S := Fintype.piFinset (fun _ : Fin k => cube T)
    (∀ r ∈ R, ∀ xs ∈ S, h r xs ∈ cube j) →
    CollisionUniversalOn S R (cube j) h →
    statDistOn (hashSupportOn S R (cube j) (repeatEval f))
      (hashActualOn S R (repeatEval f) h)
      (hashIdealOn S R (cube j) (repeatEval f))
      ≤ Real.exp (-((k : ℝ) * s ^ 2) / (8 * ((T : ℝ) + 1) ^ 2)) +
        1 / (2 : ℝ) ^ (m + 1)

/-- The numerical entropy step; the j = 0 case is included without a separate hypothesis. -/
def FloorEntropyGainStatement : Prop :=
  ∀ (T k j P : ℕ) (H Hfake s : ℝ),
    H + s ≤ Hfake → 4 ≤ (k : ℝ) * s →
    j = Nat.floor ((k : ℝ) * ((T : ℝ) - H - s / 2)) →
    ((k * T + P : ℕ) : ℝ) + 1 ≤
      (k : ℝ) * Hfake + (j : ℝ) + (P : ℝ)

def HashWidthBoundStatement : Prop :=
  ∀ (T k : ℕ) (H s : ℝ), 0 ≤ H → 0 ≤ s →
    Nat.floor ((k : ℝ) * ((T : ℝ) - H - s / 2)) ≤ k * T

end FiniteHashing

end HILL.PRG.Proposed



/-!
Proposed contracts for the product-hybrid part of HILL Lemma 4.16.

Every declaration below is a definition. A declaration ending in `Contract`
names a proposition to be proved; it does not assert that proposition. There
are no axioms, placeholders, or proof obligations hidden behind `sorry`.

The imported HILL declarations are taken from the public Prove2Me model.
The helper names and all contracts below are new proposals.
-/

namespace HILL.PRG.HybridContracts

open scoped BigOperators

/-- Concatenate the outputs on successive fixed-width seed blocks. -/
def repeatEval (F : FunEns) (k : ℕ → ℕ)
    (adv n : ℕ) (x : Bits) : Bits :=
  (List.range (k n)).flatMap fun i =>
    F.f adv n ((x.drop (i * F.t n)).take (F.t n))

/-- The actual finite uniform-source law, without a PMF conversion. -/
noncomputable def repeatLaw (F : FunEns) (a k : ℕ → ℕ)
    (n : ℕ) (z : Bits) : ℝ :=
  lawOn (cube (k n * F.t n)) (repeatEval F k (a n) n) z

/-- The repeated ensemble; its evaluation is not yet certified polynomial-time. -/
def repeatEns (F : FunEns) (k : ℕ → ℕ) : FunEns where
  t n := k n * F.t n
  ℓ n := k n * F.ℓ n
  f adv n x := repeatEval F k adv n x

/-- A product law described by the consecutive output blocks. -/
noncomputable def blockProductLaw
    (k m : ℕ) (D : Bits → ℝ) (z : Bits) : ℝ :=
  if z.length = k * m then
    ∏ i ∈ Finset.range k, D ((z.drop (i * m)).take m)
  else
    0

/-- A purely finite probability identity; no computability of k is needed. -/
def RepeatLawProductContract : Prop :=
  ∀ (F : FunEns) (a k : ℕ → ℕ), F.PTime a →
    ∀ n z,
      repeatLaw F a k n z =
        blockProductLaw (k n) (F.ℓ n) (F.law a n) z

/-- The repeated law is normalized on its declared output cube. -/
def RepeatLawProbOnContract : Prop :=
  ∀ (F : FunEns) (a k : ℕ → ℕ), F.PTime a →
    ∀ n,
      IsProbOn (cube (k n * F.ℓ n)) (repeatLaw F a k n)

/-- Shannon entropy adds across the independently sampled seed blocks. -/
def RepeatLawEntropyContract : Prop :=
  ∀ (F : FunEns) (a k : ℕ → ℕ), F.PTime a →
    ∀ n,
      shannonOn (cube (k n * F.ℓ n)) (repeatLaw F a k n) =
        (k n : ℝ) * shannonOn (cube (F.ℓ n)) (F.law a n)

/-- This is the bounded sampler-iteration machine obligation. -/
def RepeatPTimeContract : Prop :=
  ∀ (F : FunEns) (a k : ℕ → ℕ),
    F.PTime a → PTimeParam k → (repeatEns F k).PTime a

/-- Finite telescoping plus the triangle inequality, before constructing a machine. -/
def HybridStepSelectionContract : Prop :=
  ∀ (p : ℕ → ℝ) (k : ℕ), 0 < k →
    ∃ i : ℕ, i < k ∧
      |p k - p 0| ≤ (k : ℝ) * |p (i + 1) - p i|

/--
One simulator B works for all n. Its noncomputable but polynomially bounded
coin-length function may encode the selected hybrid position and A.coins n.

The statement intentionally includes n = 0 and k n = 0. In the latter case,
both repeated laws are the point mass on [], so the left side is zero.
-/
def ProductHybridContract : Prop :=
  ∀ (F W : FunEns) (a k : ℕ → ℕ),
    F.PTime a → W.PTime a → W.ℓ = F.ℓ → PTimeParam k →
    ∀ A : Adv, ∃ B : Adv, ∀ n : ℕ,
      advantage A n a (k n * F.ℓ n)
          (repeatLaw F a k n) (repeatLaw W a k n) ≤
        (k n : ℝ) *
          advantage B n a (F.ℓ n) (F.law a n) (W.law a n)

/-- The desired computational-indistinguishability corollary of the hybrid. -/
def ProductCompIndistContract : Prop :=
  ∀ (F W : FunEns) (a k : ℕ → ℕ),
    F.PTime a → W.PTime a → W.ℓ = F.ℓ → PTimeParam k →
    CompIndist a F.ℓ (F.law a) (W.law a) →
    CompIndist a (fun n => k n * F.ℓ n)
      (repeatLaw F a k) (repeatLaw W a k)

/--
Simulate a polynomially bounded target advice function using the source
adversary's coin length. No computability of b or A.coins is assumed.

Suggested construction: B.coins n = Nat.pair (b n) (A.coins n).
B computes ℓ n from unary n, splits the payload y ++ r, decodes r.length,
and gives A the first A.coins n random bits. The PTimeParam ℓ hypothesis
is what supplies the certified machine needed to locate the split.
-/
def SimulateAdviceContract : Prop :=
  ∀ (A : Adv) (a b ℓ : ℕ → ℕ),
    IsPoly b → PTimeParam ℓ →
    ∃ B : Adv, ∀ n y,
      y ∈ cube (ℓ n) →
      acceptProb B n a y = acceptProb A n b y

/-- Exact acceptance simulation implies advice-independent security here. -/
def AdviceChangeContract : Prop :=
  ∀ (a b ℓ : ℕ → ℕ) (D E : ℕ → Bits → ℝ),
    IsPoly b → PTimeParam ℓ →
    CompIndist a ℓ D E → CompIndist b ℓ D E

/-- A machine-free implication, proved by replacing acceptance probabilities. -/
def AdviceChangeFromSimulationContract : Prop :=
  SimulateAdviceContract → AdviceChangeContract

/-- Eventual domination is sufficient for all asymptotic closure arguments. -/
def EventuallyLE (u v : ℕ → ℝ) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, u n ≤ v n

def NegligibleMonoContract : Prop :=
  ∀ (u v : ℕ → ℝ),
    EventuallyLE u v → Negligible v → Negligible u

def NegligibleAddContract : Prop :=
  ∀ (u v : ℕ → ℝ),
    Negligible u → Negligible v →
    Negligible (fun n => u n + v n)

/-- No nonnegativity hypothesis on u is necessary for this upper-bound definition. -/
def NegligibleNatMulContract : Prop :=
  ∀ (q : ℕ → ℕ) (u : ℕ → ℝ),
    IsPoly q → Negligible u →
    Negligible (fun n => (q n : ℝ) * u n)

/-- PolyParam bounds only n >= 1; the single value k 0 is absorbed into a constant. -/
def PTimeParamIsPolyContract : Prop :=
  ∀ k : ℕ → ℕ, PTimeParam k → IsPoly k

/-- The hybrid-to-CI implication requires only these asymptotic closure facts. -/
def ProductCompIndistFromHybridContract : Prop :=
  ProductHybridContract →
  NegligibleMonoContract →
  NegligibleNatMulContract →
  PTimeParamIsPolyContract →
  ProductCompIndistContract

/-- Keep a j-bit prefix and pad the field to N bits with fixed zeroes. -/
def padPrefix (N j : ℕ) (u : Bits) : Bits :=
  u.take j ++ List.replicate (N - j) false

/--
Append a padded uniform j-bit field and an independent uniform p-bit key.
Sampling a full N-bit field first keeps the sampler's declared seed length
independent of j; its last N-j random bits are discarded.
-/
noncomputable def decoratedLaw
    (ℓ N j p : ℕ) (D : Bits → ℝ) (z : Bits) : ℝ :=
  weightedLaw (((cube ℓ).product (cube N)).product (cube p))
    (fun q => D q.1.1 * uniformBits N q.1.2 * uniformBits p q.2)
    (fun q => q.1.1 ++ padPrefix N j q.1.2 ++ q.2)
    z

def DecoratedLawProbOnContract : Prop :=
  ∀ (ℓ N j p : ℕ) (D : Bits → ℝ),
    j ≤ N → IsProbOn (cube ℓ) D →
    IsProbOn (cube (ℓ + N + p)) (decoratedLaw ℓ N j p D)

/-- The padded zeroes contribute no entropy; the retained key contributes p bits. -/
def DecoratedLawEntropyContract : Prop :=
  ∀ (ℓ N j p : ℕ) (D : Bits → ℝ),
    j ≤ N → IsProbOn (cube ℓ) D →
    shannonOn (cube (ℓ + N + p)) (decoratedLaw ℓ N j p D) =
      shannonOn (cube ℓ) D + (j : ℝ) + (p : ℝ)

/-- Statistical closeness implies security for arbitrary advice and lengths. -/
def StatisticalToCompIndistContract : Prop :=
  ∀ (a ℓ : ℕ → ℕ) (D E : ℕ → Bits → ℝ),
    (∀ n, IsProbOn (cube (ℓ n)) (D n)) →
    (∀ n, IsProbOn (cube (ℓ n)) (E n)) →
    Negligible (fun n => statDistOn (cube (ℓ n)) (D n) (E n)) →
    CompIndist a ℓ D E

end HILL.PRG.HybridContracts

namespace HILL.PRG.MachineContracts

/-- Escape data bits so a zero at a token boundary terminates a word. -/
def quoteBits (w : Bits) : Bits :=
  w.flatMap (fun b => [true, b])

/-- Every word, including an empty word, pays for one delimiter. -/
def encodeWords (ws : List Bits) : Bits :=
  ws.flatMap (fun w => quoteBits w ++ [false])

/-- A new word-level subroutine compiler; not a finite-alphabet symbol map. -/
def BatchCallsContract : Prop :=
  ∀ (M : Bits → Bits), PolyTimeComputable M →
    ∃ B : Bits → Bits, PolyTimeComputable B ∧
      ∀ (n a : ℕ) (xs : List Bits),
        B (encAdvice n a (encodeWords xs)) =
          encodeWords (xs.map (fun x => M (encAdvice n a x)))

/-- Certified block parsing, repeated calls and output concatenation. -/
def RepeatSamplerContract : Prop :=
  ∀ (T k : ℕ → ℕ), PTimeParam T → PTimeParam k →
    ∀ (M : Bits → Bits), PolyTimeComputable M →
      ∃ R : Bits → Bits, PolyTimeComputable R ∧
        ∀ (n a : ℕ) (xs : List Bits),
          xs.length = k n → (∀ x ∈ xs, x.length = T n) →
          R (encAdvice n a xs.flatten) =
            (xs.map (fun x => M (encAdvice n a x))).flatten

/--
Composition is an obligation in the pinned Mathlib, which marks it proof_wanted.
Prove2Me separately reports `Turing.TM2ComputableInPolyTime.comp_of_polytime`
as proved in this environment:
https://prove2.me/theorems/5b3ff7b0-a6cd-4c33-b40a-6fd6334ba249
Its accepted proof body has not been retrieved or locally certified here; the
public statement template is not imported as a proof.
-/
def CompositionContract : Prop :=
  ∀ (f g : Bits → Bits),
    PolyTimeComputable f → PolyTimeComputable g →
    PolyTimeComputable (g ∘ f)

/-- Positive unary length parameters are closed under sums and products. -/
def ParameterArithmeticContract : Prop :=
  ∀ p q : ℕ → ℕ, PTimeParam p → PTimeParam q →
    PTimeParam (fun n => p n + q n) ∧
      PTimeParam (fun n => p n * q n)

/-- A concrete, generously sized schedule; C and d are fixed constants. -/
def repetitionSchedule (C d n : ℕ) : ℕ :=
  8 * (n + 1) * (C * (n + 1) ^ d) ^ 4

def SchedulePTimeContract : Prop :=
  ∀ C d : ℕ, 0 < C → PTimeParam (repetitionSchedule C d)

end HILL.PRG.MachineContracts

namespace HILL.PRG.ConstructionContracts

open HILL.PRG.HybridContracts

def seedWidth (F : FunEns) (k : ℕ → ℕ) (n : ℕ) : ℕ :=
  k n * F.t n

/-- Full N by N affine key: N rows, each with an offset and N coefficients. -/
def keyWidth (N : ℕ) : ℕ := N * (N + 1)

def packAdvice (a j : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.pair (a n) (j n)

/-- First j rows of the fixed full affine key, with offsets first in each row. -/
def affinePrefix (N j : ℕ) (r x : Bits) : Bits :=
  (List.range j).map fun i =>
    Bool.xor (r.getD (i * (N + 1)) false)
      (ip ((r.drop (i * (N + 1) + 1)).take N) (x.take N))

/-- One uniform machine with dimensions and width supplied in unary. -/
def AffineEvaluatorContract : Prop :=
  ∃ M : Bits → Bits, PolyTimeComputable M ∧
    ∀ N j : ℕ, j ≤ N →
      ∀ r ∈ cube (keyWidth N), ∀ x ∈ cube N,
        M (encAdvice N j (r ++ x)) = affinePrefix N j r x

/-- The stronger exact independence premise used by the platform's Lemma 4.8. -/
def AffinePairwiseContract : Prop :=
  ∀ N j : ℕ, j ≤ N →
    ∀ x ∈ cube N, ∀ x' ∈ cube N, x ≠ x' →
      ∀ z ∈ cube j, ∀ z' ∈ cube j,
        ((cube (keyWidth N)).filter
          (fun r => affinePrefix N j r x = z ∧
            affinePrefix N j r x' = z')).card *
          2 ^ (2 * j) = 2 ^ keyWidth N

/--
Apply the platform's HILL.PRG.lemma_4_8 at parameter v = N, not at the
original security parameter. The fixed target j is truncated at small v.
The public theorem page reports Proved; no accepted proof is imported here:
https://prove2.me/theorems/0d655459-ea71-432d-b377-a9a49c03a0ce
-/
def fixedTargetAffine (j : ℕ) : HashFamily where
  keyLen v := keyWidth v
  inLen v := v
  outLen v := min j v
  eval v r x := affinePrefix v (min j v) r x

def AffineUniversalContract : Prop :=
  ∀ j : ℕ, (fixedTargetAffine j).IsUniversal

/-- Fixed-length output field for valid N-bit x and a sufficiently long key. -/
def paddedAffine (N j : ℕ) (r x : Bits) : Bits :=
  affinePrefix N (min j N) r x ++
    List.replicate (N - min j N) false

/-- Repeat F, hash its seed, and retain the entire independent affine key. -/
def hashGenerator (F : FunEns) (k : ℕ → ℕ) : FunEns where
  t n := seedWidth F k n + keyWidth (seedWidth F k n)
  ℓ n := k n * F.ℓ n + seedWidth F k n + keyWidth (seedWidth F k n)
  f advice n w :=
    let N := seedWidth F k n
    let a := (Nat.unpair advice).1
    let j := (Nat.unpair advice).2
    let x := w.take N
    let r := (w.drop N).take (keyWidth N)
    repeatEval F k a n x ++ paddedAffine N j r x ++ r

/--
The ideal sampler. Its N-bit uniform field is truncated to j and padded back
to N; hence its declared input length is independent of the width advice.
-/
def idealGenerator (F : FunEns) (k N : ℕ → ℕ) : FunEns where
  t n := k n * F.t n + N n + keyWidth (N n)
  ℓ n := k n * F.ℓ n + N n + keyWidth (N n)
  f advice n w :=
    let a := (Nat.unpair advice).1
    let j := min (Nat.unpair advice).2 (N n)
    let x := w.take (k n * F.t n)
    let z := (w.drop (k n * F.t n)).take (N n)
    let r := (w.drop (k n * F.t n + N n)).take (keyWidth (N n))
    repeatEval F k a n x ++ padPrefix (N n) j z ++ r

/-- Normalize n = 0, where PolyParam supplies no positivity assumption. -/
noncomputable def chosenWidth
    (F : FunEns) (a k : ℕ → ℕ) (s : ℕ → ℝ) (n : ℕ) : ℕ :=
  if n = 0 then 0 else
    Nat.floor ((k n : ℝ) *
      ((F.t n : ℝ) - shannonOn (cube (F.ℓ n)) (F.law a n) - s n / 2))

noncomputable def extractionError (n : ℕ) : ℝ :=
  Real.exp (-((n : ℝ) + 1)) + 1 / (2 : ℝ) ^ (n + 2)

/-- Pure counting; no polynomial-time premise belongs in this statement. -/
def AffineCollisionContract : Prop :=
  ∀ N j : ℕ, j ≤ N →
    ∀ x ∈ cube N, ∀ x' ∈ cube N, x ≠ x' →
      ((cube (keyWidth N)).filter
        (fun r => affinePrefix N j r x = affinePrefix N j r x')).card *
        2 ^ j = 2 ^ keyWidth N

def HashGeneratorPTimeContract : Prop :=
  ∀ (F : FunEns) (a k j : ℕ → ℕ),
    F.PTime a → PTimeParam k →
    (∀ n, j n ≤ seedWidth F k n) →
    (hashGenerator F k).PTime (packAdvice a j)

def IdealGeneratorPTimeContract : Prop :=
  ∀ (F : FunEns) (a k N j : ℕ → ℕ),
    F.PTime a → PTimeParam k → PTimeParam N →
    (∀ n, j n ≤ N n) →
    (idealGenerator F k N).PTime (packAdvice a j)

/-- Exact entropy, using only valid output lengths and finite counting. -/
def IdealGeneratorEntropyContract : Prop :=
  ∀ (F : FunEns) (a k N j : ℕ → ℕ),
    (∀ n x, x ∈ cube (F.t n) →
      (F.f (a n) n x).length = F.ℓ n) →
    (∀ n, j n ≤ N n) →
    ∀ n,
      shannonOn (cube ((idealGenerator F k N).ℓ n))
        ((idealGenerator F k N).law (packAdvice a j) n) =
      (k n : ℝ) * shannonOn (cube (F.ℓ n)) (F.law a n) +
        (j n : ℝ) + (keyWidth (N n) : ℝ)

/--
Pointwise extraction after the chosen schedule supplies these two bounds.
The j = 0 case is exact equality, and must be handled separately in its proof.
-/
def ConstructionExtractionContract : Prop :=
  ∀ (F : FunEns) (a k j : ℕ → ℕ) (s : ℕ → ℝ) (n : ℕ),
    1 ≤ n →
    (∀ x, x ∈ cube (F.t n) → (F.f (a n) n x).length = F.ℓ n) →
    0 < s n →
    j n = Nat.floor ((k n : ℝ) *
      ((F.t n : ℝ) - shannonOn (cube (F.ℓ n)) (F.law a n) - s n / 2)) →
    8 * ((n : ℝ) + 1) ≤ (k n : ℝ) * s n →
    (n : ℝ) + 1 ≤
      (k n : ℝ) * (s n) ^ 2 / (8 * ((F.t n : ℝ) + 1) ^ 2) →
    statDistOn (cube ((hashGenerator F k).ℓ n))
      ((hashGenerator F k).law (packAdvice a j) n)
      ((idealGenerator F k (seedWidth F k)).law (packAdvice a j) n) ≤
        extractionError n

/-- Product hybrid, advice simulation, and padded uniform postprocessing. -/
def ConstructionCompIndistContract : Prop :=
  ∀ (F W : FunEns) (a k j : ℕ → ℕ),
    F.PTime a → W.PTime a → W.ℓ = F.ℓ → PTimeParam k →
    (∀ n, j n ≤ seedWidth F k n) →
    CompIndist a F.ℓ (F.law a) (W.law a) →
    CompIndist (packAdvice a j) (hashGenerator F k).ℓ
      ((idealGenerator F k (seedWidth F k)).law (packAdvice a j))
      ((idealGenerator W k (seedWidth F k)).law (packAdvice a j))

def ExtractionErrorNegligibleContract : Prop := Negligible extractionError

end HILL.PRG.ConstructionContracts

namespace HILL.PRG.InterfaceConsequences

open HILL.PRG.HybridContracts

/-- This elementary asymptotic consequence has a proof body. -/
theorem negligibleMono : NegligibleMonoContract := by
  intro u v huv hv k
  obtain ⟨N₀, h₀⟩ := huv
  obtain ⟨N₁, h₁⟩ := hv k
  refine ⟨max N₀ N₁, ?_⟩
  intro n hn
  exact lt_of_le_of_lt
    (h₀ n (le_trans (le_max_left _ _) hn))
    (h₁ n (le_trans (le_max_right _ _) hn))

/-- Only the simulator is assumed; replacing the acceptance weights is proved. -/
theorem adviceChange_of_simulation
    (hsim : SimulateAdviceContract) : AdviceChangeContract := by
  intro a b ℓ D E hb hℓ hCI A
  obtain ⟨B, hB⟩ := hsim A a b ℓ hb hℓ
  have hEq : ∀ n,
      advantage A n b (ℓ n) (D n) (E n) =
        advantage B n a (ℓ n) (D n) (E n) := by
    intro n
    unfold advantage
    apply congrArg abs
    apply Finset.sum_congr rfl
    intro y hy
    rw [hB n y hy]
  simpa only [hEq] using hCI B

/-- The finite quantitative hybrid implies product security using explicit closures. -/
theorem productCompIndist_of_hybrid
    (hhybrid : ProductHybridContract)
    (hmul : NegligibleNatMulContract)
    (hpoly : PTimeParamIsPolyContract) : ProductCompIndistContract := by
  intro F W a k hF hW hlen hk hCI A
  obtain ⟨B, hB⟩ := hhybrid F W a k hF hW hlen hk A
  apply negligibleMono _ _
    (show EventuallyLE _ _ from ⟨0, fun n _ => hB n⟩)
  exact hmul k _ (hpoly k hk) (hCI B)

/-- The target can take the constant gap one. -/
theorem polyParam_one : PolyParam (fun _ => 1) := by
  refine ⟨1, by decide, ?_⟩
  intro n hn
  have hnR : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr hn
  simp only [Nat.cast_one, pow_one, one_mul]
  constructor
  · apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hnR)).2
    simpa using hnR
  · exact hnR

/-- Direct unpacking of the exact model, with every substantive premise explicit. -/
theorem pseudoentropy_of_witness
    (G V : FunEns) (b : ℕ → ℕ)
    (hG : G.PTime b) (hV : V.PTime b)
    (hlen : V.ℓ = G.ℓ)
    (hparam : PolyParam (fun n => (G.t n : ℝ) + 1))
    (hCI : CompIndist b G.ℓ (G.law b) (V.law b))
    (hentropy : ∃ N : ℕ, ∀ n ≥ N, 1 ≤ n →
      (G.t n : ℝ) + 1 ≤ shannonOn (cube (G.ℓ n)) (V.law b n)) :
    PolyParam (fun _ => 1) ∧ IsPseudoentropyGen G b (fun _ => 1) := by
  exact ⟨polyParam_one, hG, hparam, V, hV, hlen, hCI, hentropy⟩

end HILL.PRG.InterfaceConsequences

end HILL416_Contracts

section HILL416_Statistical

namespace HILL.PRG

theorem negligible_add {r s : ℕ → ℝ} (hr : Negligible r) (hs : Negligible s) :
    Negligible (fun n => r n + s n) := by
  intro k
  obtain ⟨N, hN⟩ := hr (k + 1)
  obtain ⟨M, hM⟩ := hs (k + 1)
  refine ⟨max N (max M 2), ?_⟩
  intro n hn
  have htwo : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
  have hpow : 0 < (n : ℝ) ^ k := pow_pos (by linarith) k
  have hscale : (1 : ℝ) / (n : ℝ) ^ (k + 1) ≤ 1 / (2 * (n : ℝ) ^ k) :=
    one_div_le_one_div_of_le (mul_pos (by norm_num) hpow)
      (by
        rw [pow_succ, mul_comm (2 : ℝ) ((n : ℝ) ^ k)]
        exact mul_le_mul_of_nonneg_left htwo hpow.le)
  have hsum := add_lt_add ((hN n (by omega)).trans_le hscale) ((hM n (by omega)).trans_le hscale)
  calc
    _ < _ := hsum
    _ = _ := by ring

private theorem acceptProb_bounds (A : Adv) (n : ℕ) (a : ℕ → ℕ) (y : Bits) :
    0 ≤ acceptProb A n a y ∧ acceptProb A n a y ≤ 1 := by
  unfold acceptProb uniformProb
  constructor
  · positivity
  · exact div_le_one_of_le₀
      (Nat.cast_le.mpr (Finset.card_filter_le _ _)) (Nat.cast_nonneg _)

/-- Bounded acceptance weights relate the exact HILL advantage and statistical distance. -/
theorem advantage_le_twice_statDist (A : Adv) (n : ℕ) (a : ℕ → ℕ)
    (ℓ : ℕ) (D E : Bits → ℝ) :
    advantage A n a ℓ D E ≤ 2 * statDistOn (cube ℓ) D E := by
  unfold advantage statDistOn
  calc
    _ ≤ ∑ y ∈ cube ℓ, |(D y - E y) * acceptProb A n a y| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ y ∈ cube ℓ, |D y - E y| := by
      apply Finset.sum_le_sum
      exact fun y _ => by
        simpa only [abs_mul, abs_of_nonneg (acceptProb_bounds A n a y).1] using
          mul_le_of_le_one_right (abs_nonneg (D y - E y)) (acceptProb_bounds A n a y).2
    _ = _ := by ring

/-- Statistical closeness suffices for computational indistinguishability in the HILL model. -/
theorem compIndist_of_negligible_statDist
    (a ℓ : ℕ → ℕ) (D E : ℕ → Bits → ℝ)
    (h : Negligible (fun n => statDistOn (cube (ℓ n)) (D n) (E n))) :
    CompIndist a ℓ D E := by
  intro A
  exact InterfaceConsequences.negligibleMono _ _
    ⟨0, fun n _ => by simpa only [two_mul] using
      advantage_le_twice_statDist A n a (ℓ n) (D n) (E n)⟩
    (negligible_add h h)

/-- Computational indistinguishability composes along a chain of intermediate laws. -/
theorem compIndist_trans {a ℓ : ℕ → ℕ} {D E F : ℕ → Bits → ℝ}
    (hDE : CompIndist a ℓ D E) (hEF : CompIndist a ℓ E F) :
    CompIndist a ℓ D F := by
  intro A
  apply InterfaceConsequences.negligibleMono
    (v := fun n => advantage A n a (ℓ n) (D n) (E n) +
      advantage A n a (ℓ n) (E n) (F n)) _ ?_ (negligible_add (hDE A) (hEF A))
  refine ⟨0, ?_⟩
  intro n _
  unfold advantage
  have hsum :
      (∑ y ∈ cube (ℓ n), (D n y - F n y) * acceptProb A n a y) =
        (∑ y ∈ cube (ℓ n), (D n y - E n y) * acceptProb A n a y) +
        (∑ y ∈ cube (ℓ n), (E n y - F n y) * acceptProb A n a y) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  simpa only [hsum] using (abs_add_le
    (∑ y ∈ cube (ℓ n), (D n y - E n y) * acceptProb A n a y)
    (∑ y ∈ cube (ℓ n), (E n y - F n y) * acceptProb A n a y))

end HILL.PRG

end HILL416_Statistical

section HILL416_Parameters

open Filter
open scoped Topology

namespace HILL.PRG

open MachineContracts ConstructionContracts

/-- A constant and exponent depending only on the original polynomial bounds
give both numerical inequalities required by the extraction step. -/
theorem repetitionSchedule_bounds {T : ℕ → ℕ} {s : ℕ → ℝ}
    (hT : PolyParam (fun n => (T n : ℝ))) (hs : PolyParam s) :
    ∃ C d : ℕ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      0 < s n ∧
      8 * ((n : ℝ) + 1) ≤ (repetitionSchedule C d n : ℝ) * s n ∧
      (n : ℝ) + 1 ≤
        (repetitionSchedule C d n : ℝ) * (s n) ^ 2 /
          (8 * ((T n : ℝ) + 1) ^ 2) := by
  obtain ⟨cT, hcT, hT⟩ := hT
  obtain ⟨cs, hcs, hs⟩ := hs
  let C := max (cT + 1) cs
  let d := max cT cs
  refine ⟨C, d, hcT.trans_le (by dsimp [C]; omega), ?_⟩
  intro n hn
  let q : ℝ := (C : ℝ) * ((n : ℝ) + 1) ^ d
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpow (c : ℕ) (hc : c ≤ d) : (n : ℝ) ^ c ≤ ((n : ℝ) + 1) ^ d :=
    (pow_le_pow_left₀ (by positivity) (by linarith) _).trans
      (pow_le_pow_right₀ (by linarith) hc)
  have hTq : (T n : ℝ) + 1 ≤ q := by
    have hbase : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ d := one_le_pow₀ (by linarith)
    have hm := mul_le_mul_of_nonneg_left (hpow cT (le_max_left _ _))
      (Nat.cast_nonneg (α := ℝ) cT)
    have hC : (cT : ℝ) + 1 ≤ C := by exact_mod_cast le_max_left (cT + 1) cs
    calc
      _ ≤ (cT : ℝ) * (n : ℝ) ^ cT + 1 := add_le_add_left (hT n hn).2 _
      _ ≤ (cT : ℝ) * ((n : ℝ) + 1) ^ d + ((n : ℝ) + 1) ^ d := add_le_add hm hbase
      _ = ((cT : ℝ) + 1) * ((n : ℝ) + 1) ^ d := by ring
      _ ≤ q := mul_le_mul_of_nonneg_right hC (by positivity)
  have hsq : (cs : ℝ) * (n : ℝ) ^ cs ≤ q :=
    mul_le_mul (by exact_mod_cast le_max_right (cT + 1) cs)
      (hpow cs (le_max_right _ _)) (by positivity) (by positivity)
  have hden : 0 < (cs : ℝ) * (n : ℝ) ^ cs :=
    mul_pos (Nat.cast_pos.mpr hcs) (pow_pos (by linarith) _)
  have hsn : 0 < s n := (one_div_pos.mpr hden).trans_le (hs n hn).1
  have hqsn : 1 ≤ q * s n :=
    (by simpa only [mul_comm ((cs : ℝ) * (n : ℝ) ^ cs)] using
      (div_le_iff₀ hden).mp (hs n hn).1 : 1 ≤ ((cs : ℝ) * (n : ℝ) ^ cs) * s n).trans
      (mul_le_mul_of_nonneg_right hsq hsn.le)
  have hq : 1 ≤ q := (show (1 : ℝ) ≤ (T n : ℝ) + 1 by linarith [Nat.cast_nonneg (α := ℝ) (T n)]).trans hTq
  have hq4 : 1 ≤ q ^ 4 * s n :=
    hqsn.trans (mul_le_mul_of_nonneg_right
      (le_self_pow₀ hq (by decide : (4 : ℕ) ≠ 0)) hsn.le)
  have hq22 : 1 ≤ (q * s n) ^ 2 := one_le_pow₀ hqsn
  have hvar : ((T n : ℝ) + 1) ^ 2 ≤ q ^ 4 * (s n) ^ 2 := calc
    _ ≤ q ^ 2 := pow_le_pow_left₀ (by positivity) hTq _
    _ ≤ q ^ 2 * (q * s n) ^ 2 := le_mul_of_one_le_right (by positivity) hq22
    _ = _ := by ring
  have hk : (repetitionSchedule C d n : ℝ) = 8 * ((n : ℝ) + 1) * q ^ 4 := by
    simp [repetitionSchedule, q]
  refine ⟨hsn, ?_, ?_⟩
  · rw [hk, mul_assoc]
    exact le_mul_of_one_le_right (by positivity) hq4
  · rw [hk, le_div_iff₀ (by positivity)]
    calc
      _ = 8 * ((n : ℝ) + 1) * ((T n : ℝ) + 1) ^ 2 := by ring
      _ ≤ 8 * ((n : ℝ) + 1) * (q ^ 4 * (s n) ^ 2) :=
        mul_le_mul_of_nonneg_left hvar (by positivity)
      _ = _ := by ring

theorem floorEntropyGain : Proposed.FloorEntropyGainStatement := by
  intro T k j P H Hfake s hW hk hj
  have hround := Nat.lt_floor_add_one ((k : ℝ) * ((T : ℝ) - H - s / 2))
  rw [← hj] at hround
  push_cast
  nlinarith [mul_le_mul_of_nonneg_left hW (Nat.cast_nonneg (α := ℝ) k)]

theorem hashWidthBound : Proposed.HashWidthBoundStatement := by
  intro T k H s hH hs
  apply Nat.floor_le_of_le
  push_cast
  exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg k)

private theorem negligibleExp (c : ℝ) (hc : 0 < c) :
    Negligible (fun n => Real.exp (-(n : ℝ) * c)) := by
  intro j
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (j : ℝ) c hc
  simp_rw [Real.rpow_natCast, neg_mul, mul_comm c] at h
  have hSmall := (h.comp tendsto_natCast_atTop_atTop).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hSmall
  refine ⟨max 1 N, ?_⟩
  intro n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [lt_div_iff₀ (pow_pos hnR _), mul_comm]
  simpa only [Function.comp_apply, neg_mul] using hN n (le_trans (le_max_right 1 N) hn)

theorem extractionErrorNegligible : ExtractionErrorNegligibleContract := by
  apply InterfaceConsequences.negligibleMono
    (v := fun n => Real.exp (-(n : ℝ) * 1) + Real.exp (-(n : ℝ) * Real.log 2))
  · refine ⟨0, fun n _ => add_le_add ?_ ?_⟩
    · apply Real.exp_le_exp.mpr
      linarith
    · rw [show (1 : ℝ) / 2 ^ (n + 2) = Real.exp (-((n : ℝ) + 2) * Real.log 2) by
        have hcast : ((n : ℝ) + 2) = ((n + 2 : ℕ) : ℝ) := by push_cast; rfl
        rw [one_div, hcast, neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num)]]
      exact Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right (by linarith) (Real.log_nonneg (by norm_num)))
  · exact negligible_add (negligibleExp 1 one_pos) (negligibleExp _ (Real.log_pos (by norm_num)))

theorem shannonOn_lawOn_nonneg {α β : Type*} [DecidableEq β]
    (S : Finset α) (Y : Finset β) (g : α → β) : 0 ≤ shannonOn Y (lawOn S g) := by
  apply Finset.sum_nonneg
  intro y _
  have h0 : 0 ≤ lawOn S g y := by unfold lawOn; positivity
  have h1 : lawOn S g y ≤ 1 := by
    unfold lawOn
    exact div_le_one_of_le₀ (Nat.cast_le.mpr (Finset.card_filter_le _ _)) (Nat.cast_nonneg _)
  exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos h0 (Real.logb_nonpos (by norm_num) h0 h1))

end HILL.PRG

end HILL416_Parameters

section HILL416_ScheduleMachine

namespace HILL.PRG

open MachineContracts CLRS.Chapter34.Turing.PolyBuilder

private theorem schedulePolyParam (C d : ℕ) (hC : 0 < C) :
    PolyParam (fun n => (repetitionSchedule C d n : ℝ)) := by
  let e := 4 * d + 1
  let B := 16 * (C * 2 ^ d) ^ 4
  let c := max e B
  have hc : 0 < c := by dsimp [c, e]; omega
  refine ⟨c, hc, ?_⟩
  intro n hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hB : (B : ℝ) ≤ c := Nat.cast_le.mpr (le_max_right _ _)
  have hPow : (n : ℝ) ^ e ≤ (n : ℝ) ^ c :=
    pow_le_pow_right₀ hnR (le_max_left _ _)
  have hUpper : (repetitionSchedule C d n : ℝ) ≤ (B : ℝ) * (n : ℝ) ^ e := by
    simp only [repetitionSchedule, Nat.cast_mul, Nat.cast_pow, Nat.cast_add,
      Nat.cast_ofNat, Nat.cast_one]
    calc
      _ ≤ 8 * (2 * (n : ℝ)) * ((C : ℝ) * (2 * (n : ℝ)) ^ d) ^ 4 := by
        have hb : (n : ℝ) + 1 ≤ 2 * n := by linarith
        gcongr
      _ = (B : ℝ) * (n : ℝ) ^ e := by
        dsimp [B, e]
        push_cast
        rw [pow_add, pow_one, Nat.mul_comm 4 d, pow_mul]
        simp only [mul_pow]
        ring
  have hPositive : (1 : ℝ) ≤ (repetitionSchedule C d n : ℝ) := by
    exact_mod_cast (show 1 ≤ repetitionSchedule C d n by
      apply Nat.succ_le_of_lt
      unfold repetitionSchedule
      positivity)
  have hcR : (1 : ℝ) ≤ c := Nat.one_le_cast.mpr hc
  refine ⟨?_, hUpper.trans (mul_le_mul hB hPow (by positivity) (by positivity))⟩
  have hden : (1 : ℝ) ≤ (c : ℝ) * (n : ℝ) ^ c :=
    one_le_mul_of_one_le_of_one_le hcR (one_le_pow₀ hnR)
  exact (div_le_one_of_le₀ hden (zero_le_one.trans hden)).trans hPositive

private theorem unitClock_as_true (xs : List Unit) :
    xs.flatMap (fun _ => [true]) = List.replicate xs.length true := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih, List.replicate_succ]

/-- Evaluate the scheduled repetition count in unary with a verified fixed
polynomial clock in the same TM2 model used by HILL. -/
theorem schedulePTime : SchedulePTimeContract := by
  intro C d hC
  refine ⟨schedulePolyParam C d hC, ?_⟩
  let p : Polynomial ℕ := 8 * (Polynomial.X + 1) *
    (Polynomial.C C * (Polynomial.X + 1) ^ d) ^ 4
  let outputBody : LoopBody Unit Bool := ⟨fun _ => [true], fun _ => 1, fun _ => by decide⟩
  have h := _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
    (exactPolynomialClock_computableInPolyTime (Γ := Bool) p)
    (boundedLoop_computableInPolyTime outputBody)
  have hFunction : ((fun input => input.flatMap outputBody.emit) ∘
        exactPolynomialClock (Γ := Bool) p) =
      fun w => List.replicate (repetitionSchedule C d w.length) true := by
    funext w
    simp [outputBody, unitClock_as_true, exactPolynomialClock_length,
      p, repetitionSchedule]
  exact hFunction ▸ h

end HILL.PRG

end HILL416_ScheduleMachine

section HILL416_ParameterMachine

namespace HILL.PRG

open MachineContracts CLRS.Chapter34.Turing.PolyBuilder Turing.TM2Comp

private theorem polynomialParameterArithmetic {p q : ℕ → ℕ}
    (hp : PolyParam (fun n => (p n : ℝ))) (hq : PolyParam (fun n => (q n : ℝ))) :
    PolyParam (fun n => ((p n + q n : ℕ) : ℝ)) ∧
      PolyParam (fun n => ((p n * q n : ℕ) : ℝ)) := by
  obtain ⟨a, ha, hp⟩ := hp
  obtain ⟨b, hb, hq⟩ := hq
  let c := a + b + a * b
  have hc : 0 < c := by dsimp [c]; omega
  have bounds (n : ℕ) (hn : 1 ≤ n) :
      1 / ((c : ℝ) * (n : ℝ) ^ c) ≤ 1 ∧
      1 ≤ (p n : ℝ) ∧ 1 ≤ (q n : ℝ) ∧
      (p n : ℝ) + q n ≤ (c : ℝ) * (n : ℝ) ^ c ∧
      (p n : ℝ) * q n ≤ (c : ℝ) * (n : ℝ) ^ c := by
    have hnR : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr hn
    have hD : (1 : ℝ) ≤ (c : ℝ) * (n : ℝ) ^ c :=
      one_le_mul_of_one_le_of_one_le (Nat.one_le_cast.mpr hc) (one_le_pow₀ hnR)
    have hp1 : (1 : ℝ) ≤ p n := by
      have h : (0 : ℝ) < p n := (one_div_pos.mpr (by positivity)).trans_le (hp n hn).1
      exact Nat.one_le_cast.mpr (Nat.cast_pos.mp h)
    have hq1 : (1 : ℝ) ≤ q n := by
      have h : (0 : ℝ) < q n := (one_div_pos.mpr (by positivity)).trans_le (hq n hn).1
      exact Nat.one_le_cast.mpr (Nat.cast_pos.mp h)
    refine ⟨div_le_one_of_le₀ hD (zero_le_one.trans hD), hp1, hq1, ?_, ?_⟩
    · have h₁ : (n : ℝ) ^ a ≤ (n : ℝ) ^ c :=
        pow_le_pow_right₀ hnR (by dsimp [c]; omega)
      have h₂ : (n : ℝ) ^ b ≤ (n : ℝ) ^ c :=
        pow_le_pow_right₀ hnR (by dsimp [c]; omega)
      calc
        _ ≤ (a : ℝ) * (n : ℝ) ^ a + (b : ℝ) * (n : ℝ) ^ b :=
          add_le_add (hp n hn).2 (hq n hn).2
        _ ≤ (a : ℝ) * (n : ℝ) ^ c + (b : ℝ) * (n : ℝ) ^ c :=
          add_le_add (mul_le_mul_of_nonneg_left h₁ (by positivity))
            (mul_le_mul_of_nonneg_left h₂ (by positivity))
        _ ≤ _ := by
          rw [← add_mul]
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          dsimp [c]
          push_cast
          linarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) a) (Nat.cast_nonneg (α := ℝ) b)]
    · calc
        _ ≤ ((a : ℝ) * (n : ℝ) ^ a) * ((b : ℝ) * (n : ℝ) ^ b) :=
          mul_le_mul (hp n hn).2 (hq n hn).2 (by positivity) (by positivity)
        _ = ((a * b : ℕ) : ℝ) * (n : ℝ) ^ (a + b) := by rw [pow_add]; push_cast; ring
        _ ≤ _ := mul_le_mul
          (Nat.cast_le.mpr (by dsimp [c]; omega))
          (pow_le_pow_right₀ hnR (by dsimp [c]; omega)) (by positivity) (by positivity)
  constructor
  · refine ⟨c, hc, fun n hn => ?_⟩
    obtain ⟨hd, hpn, hqn, hSum, _⟩ := bounds n hn
    push_cast
    exact ⟨hd.trans (by linarith), hSum⟩
  · refine ⟨c, hc, fun n hn => ?_⟩
    obtain ⟨hd, hpn, hqn, _, hProd⟩ := bounds n hn
    push_cast
    exact ⟨hd.trans (one_le_mul_of_one_le_of_one_le hpn hqn), hProd⟩

private def tagBody (tag : UnaryFrameSym) : LoopBody Bool UnaryFrameSym :=
  ⟨fun _ => [tag], fun _ => 1, fun _ => by simp⟩

private def addBody : LoopBody UnaryFrameSym Bool :=
  ⟨fun _ => [true], fun _ => 1, fun _ => by decide⟩

private def mulBody : LoopBody (UnaryFrameSym × UnaryFrameSym) Bool where
  emit q := if q.1 = .tick ∧ q.2 = .separator then [true] else []
  cost _ := 1
  emit_length_le_cost q := by split <;> decide

private theorem addBody_runs (u v : ℕ) :
    ((List.replicate u .tick ++ List.replicate v .separator) :
      List UnaryFrameSym).flatMap addBody.emit = List.replicate (u+v) true := by
  simp [addBody, List.flatMap_append, List.flatMap_replicate]

private theorem mulBody_runs (u v : ℕ) :
    nestedLoopOutput mulBody (List.replicate u .tick ++ List.replicate v .separator) =
      List.replicate (u*v) true := by
  simp [nestedLoopOutput, mulBody, List.flatMap_append, List.flatMap_replicate]

private theorem tagBody_runs (tag : UnaryFrameSym) (w : Bits) :
    w.flatMap (tagBody tag).emit = List.replicate w.length tag := by
  induction w with
  | nil => rfl
  | cons b w ih => exact congrArg (tag :: ·) ih

/-- Multiply two lengths computed from the same input, returning the result in unary. -/
theorem polytime_unary_product {f g : Bits → Bits}
    (hf : PolyTimeComputable f) (hg : PolyTimeComputable g) :
    PolyTimeComputable (fun w => List.replicate ((f w).length * (g w).length) true) := by
  obtain ⟨F⟩ := hf
  obtain ⟨G⟩ := hg
  let left := Classical.choice (TM2ComputableInPolyTime.comp_scratch F
    (boundedLoop_computableInPolyTime (tagBody .tick)))
  let right := Classical.choice (TM2ComputableInPolyTime.comp_scratch G
    (boundedLoop_computableInPolyTime (tagBody .separator)))
  let both := unaryFrameSameInputConcat_computableInPolyTime left right
  have h := TM2ComputableInPolyTime.comp_scratch both (nestedLoop_computableInPolyTime mulBody)
  simpa only [Levin2003.PolyTimeComputable, Function.comp_def, tagBody_runs, mulBody_runs] using h

/-- Addition and multiplication of length parameters have uniform TM2 certificates. -/
theorem parameterArithmetic : ParameterArithmeticContract := by
  intro p q hp hq
  have hPoly := polynomialParameterArithmetic hp.1 hq.1
  obtain ⟨P⟩ := hp.2
  obtain ⟨Q⟩ := hq.2
  let left := Classical.choice (TM2ComputableInPolyTime.comp_scratch P
    (boundedLoop_computableInPolyTime (tagBody .tick)))
  let right := Classical.choice (TM2ComputableInPolyTime.comp_scratch Q
    (boundedLoop_computableInPolyTime (tagBody .separator)))
  let both := unaryFrameSameInputConcat_computableInPolyTime left right
  have hAdd := TM2ComputableInPolyTime.comp_scratch both
    (boundedLoop_computableInPolyTime addBody)
  have hMul := TM2ComputableInPolyTime.comp_scratch both
    (nestedLoop_computableInPolyTime mulBody)
  refine ⟨⟨hPoly.1, ?_⟩, ⟨hPoly.2, ?_⟩⟩
  · simpa only [Levin2003.PolyTimeComputable, Function.comp_def, tagBody, List.flatMap_replicate,
      List.flatten_replicate_singleton, addBody_runs] using hAdd
  · simpa only [Levin2003.PolyTimeComputable, Function.comp_def, tagBody, List.flatMap_replicate,
      List.flatten_replicate_singleton, mulBody_runs] using hMul

end HILL.PRG

end HILL416_ParameterMachine

section HILL416_Fibers

namespace HILL.PRG.Proposed

open scoped BigOperators

variable {α β : Type*} [DecidableEq β]

theorem productFiber : ProductFiberStatement (α := α) (β := β) := by
  intro S f k ys
  unfold fiberCardOn
  rw [← Fintype.card_piFinset]
  congr 1
  exact Finset.ext fun xs => by simp [Fintype.mem_piFinset, funext_iff, forall_and]

theorem logFiberBounds : LogFiberBoundsStatement (α := α) (β := β) := by
  intro S f x hx
  have hxF : x ∈ S.filter (fun z => f z = f x) := Finset.mem_filter.mpr ⟨hx, rfl⟩
  have hPos : (1 : ℝ) ≤ (fiberCardOn S f (f x) : ℝ) :=
    Nat.one_le_cast.mpr (Finset.card_pos.mpr ⟨x, hxF⟩)
  exact ⟨Real.logb_nonneg (by norm_num) hPos,
    Real.logb_le_logb_of_le (by norm_num) (zero_lt_one.trans_le hPos)
      (Nat.cast_le.mpr (Finset.card_filter_le S _))⟩

theorem entropyOfOnSuperset : EntropyOfOnSupersetStatement (α := α) (β := β) := by
  intro S B f hf
  unfold entropyOf shannonOn
  refine Finset.sum_subset (Finset.image_subset_iff.mpr hf) ?_
  intro y _ hy
  have hempty : S.filter (fun x => f x = y) = ∅ :=
    Finset.filter_eq_empty_iff.mpr (fun x hx he => hy (Finset.mem_image.mpr ⟨x, hx, he⟩))
  simp [lawOn, hempty]

theorem meanLogFiber : MeanLogFiberStatement (α := α) (β := β) := by
  intro S f hS
  have hSpos : (0 : ℝ) < S.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hS)
  have hpartition : (∑ y ∈ S.image f, lawOn S f y) = 1 := by
    simp only [lawOn, ← Finset.sum_div, ← Nat.cast_sum,
      ← Finset.card_eq_sum_card_image f S, div_self hSpos.ne']
  have hmean :
      averageOn S (logFiberOn S f) =
        ∑ y ∈ S.image f, lawOn S f y * Real.logb 2 (fiberCardOn S f y : ℝ) := by
    unfold averageOn logFiberOn
    rw [← Finset.sum_fiberwise_of_maps_to' (fun x hx => Finset.mem_image_of_mem f hx)
      (fun y => Real.logb 2 (fiberCardOn S f y : ℝ)), Finset.sum_div]
    exact Finset.sum_congr rfl fun y _ => by
      simp only [Finset.sum_const, nsmul_eq_mul, lawOn, fiberCardOn, div_mul_eq_mul_div]
  rw [hmean, entropyOf, shannonOn]
  have hlog (y : β) (hy : y ∈ S.image f) :
      Real.logb 2 (lawOn S f y) =
        Real.logb 2 (fiberCardOn S f y : ℝ) - Real.logb 2 (S.card : ℝ) := by
    obtain ⟨x, hx, hfx⟩ := Finset.mem_image.mp hy
    exact Real.logb_div
      (Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hfx⟩⟩))
      hSpos.ne'
  have hExpand :
      (∑ y ∈ S.image f, -(lawOn S f y * Real.logb 2 (lawOn S f y))) =
        ∑ y ∈ S.image f,
          -(lawOn S f y * (Real.logb 2 (fiberCardOn S f y : ℝ) -
            Real.logb 2 (S.card : ℝ))) :=
    Finset.sum_congr rfl (fun y hy => by rw [hlog y hy])
  rw [hExpand]
  simp_rw [mul_sub, neg_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
    hpartition, one_mul, sub_sub_cancel]

end HILL.PRG.Proposed

end HILL416_Fibers

section HILL416_Blocks

namespace HILL.PRG

theorem mem_cube_iff_length {x : Bits} {T : ℕ} : x ∈ cube T ↔ x.length = T := by
  unfold cube Levin2003.cube
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨v, rfl⟩
    simp
  · intro h
    subst T
    exact ⟨fun i => x[i.val], List.ofFn_getElem⟩

namespace Blocks

def flatten {k : ℕ} (xs : Fin k → Bits) : Bits := (List.ofFn xs).flatten

def block {k : ℕ} (T : ℕ) (x : Bits) (i : Fin k) : Bits :=
  (x.drop (i.val * T)).take T

theorem flatten_length {k T : ℕ} (xs : Fin k → Bits)
    (hx : ∀ i, (xs i).length = T) : (flatten xs).length = k * T := by
  induction k with
  | zero => simp [flatten]
  | succ k ih =>
    simp only [flatten, List.ofFn_succ, List.flatten_cons, List.length_append, hx]
    rw [← flatten, ih _ (fun i => hx i.succ), Nat.succ_mul, Nat.add_comm]

theorem block_length {k T : ℕ} {x : Bits} (h : x.length = k * T) (i : Fin k) :
    (block T x i).length = T := by
  have hbound : (i.val + 1) * T ≤ k * T := Nat.mul_le_mul_right T i.isLt
  rw [Nat.add_mul, one_mul] at hbound
  simpa [block, h] using (Nat.min_eq_left (show T ≤ k * T - i.val * T by omega))

theorem block_flatten {k T : ℕ} (xs : Fin k → Bits)
    (hx : ∀ i, (xs i).length = T) (i : Fin k) : block T (flatten xs) i = xs i := by
  induction k with
  | zero => exact Fin.elim0 i
  | succ k ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [block, flatten, List.ofFn_succ] using
        List.take_left' (l₂ := flatten (fun i : Fin k => xs i.succ)) (hx 0)
    · have hdrop : (flatten xs).drop T = flatten (fun i : Fin k => xs i.succ) := by
        simpa [flatten, List.ofFn_succ] using
          List.drop_left' (l₂ := flatten (fun i : Fin k => xs i.succ)) (hx 0)
      change ((flatten xs).drop ((j.val + 1) * T)).take T = xs j.succ
      rw [Nat.add_mul, one_mul, Nat.add_comm (j.val * T) T, ← List.drop_drop, hdrop]
      exact ih _ (fun i => hx i.succ) j

theorem flatten_block {k T : ℕ} {x : Bits} (h : x.length = k * T) :
    flatten (block (k := k) T x) = x := by
  induction k generalizing x with
  | zero => exact (List.length_eq_zero_iff.mp (by simpa using h)).symm
  | succ k ih =>
    have hTail : (x.drop T).length = k * T := by
      simp [h, Nat.succ_mul]
    have hBlock (i : Fin k) : block T x i.succ = block T (x.drop T) i := by
      simp [block, Nat.add_mul, Nat.add_comm, List.drop_drop]
    simp only [flatten, List.ofFn_succ, List.flatten_cons, hBlock]
    have hHead : block T x (0 : Fin (k + 1)) = x.take T := by simp [block]
    rw [hHead]
    change x.take T ++ flatten (block (k := k) T (x.drop T)) = x
    rw [ih hTail, List.take_append_drop]

theorem flatten_bijOn (k T : ℕ) :
    Set.BijOn (flatten (k := k)) (↑(Fintype.piFinset (fun _ : Fin k => cube T)) : Set (Fin k → Bits))
      (cube (k * T) : Set Bits) := by
  have hl (xs : Fin k → Bits) (hxs : xs ∈ Fintype.piFinset (fun _ => cube T)) :
      ∀ i, (xs i).length = T := fun i => mem_cube_iff_length.mp (Fintype.mem_piFinset.mp hxs i)
  refine ⟨?_, ?_, ?_⟩
  · exact fun xs hxs => mem_cube_iff_length.mpr (flatten_length xs (hl xs hxs))
  · intro x hx y hy hxy
    funext i
    rw [← block_flatten x (hl x hx) i, hxy, block_flatten y (hl y hy) i]
  · intro x hx
    exact ⟨block T x, Fintype.mem_piFinset.mpr (fun i =>
      mem_cube_iff_length.mpr (block_length (mem_cube_iff_length.mp hx) i)),
      flatten_block (mem_cube_iff_length.mp hx)⟩

end Blocks
end HILL.PRG

end HILL416_Blocks

section HILL416_Hoeffding

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

namespace HILL.PRG.Proposed

private theorem uniformPi {A : Type*} [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A] (k : ℕ) :
    (Measure.pi fun _ : Fin k => (PMF.uniformOfFintype A).toMeasure) =
      (PMF.uniformOfFintype (Fin k → A)).toMeasure := by
  apply Measure.ext_of_singleton
  intro x
  rw [Measure.pi_singleton]
  simp_rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _),
    PMF.uniformOfFintype_apply]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Fintype.card_fun, Nat.cast_pow, ENNReal.inv_pow]

private theorem integral_uniformFintype {A : Type*} [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A] (W : A → ℝ) :
    ∫ x, W x ∂(PMF.uniformOfFintype A).toMeasure =
      (∑ x, W x) / (Fintype.card A : ℝ) := by
  rw [PMF.integral_eq_sum]
  simp [ENNReal.toReal_inv, div_eq_mul_inv, mul_comm, Finset.sum_mul]

private theorem finiteUniformLowerTail {A : Type*} [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (W : A → ℝ) {B η : ℝ} (hB : 0 < B) (hη : 0 ≤ η)
    (hW : ∀ x, W x ∈ Set.Icc 0 B) {k : ℕ} (hk : 0 < k) :
    let μ := (PMF.uniformOfFintype (Fin k → A)).toMeasure
    μ.real {x | (∑ i : Fin k, W (x i)) <
      (k : ℝ) * ((∑ z, W z) / (Fintype.card A : ℝ) - η)} ≤
      Real.exp (-(2 * (k : ℝ) * η ^ 2) / B ^ 2) := by
  dsimp only
  rw [← uniformPi]
  let μ := (PMF.uniformOfFintype A).toMeasure
  let ν := Measure.pi fun _ : Fin k => μ
  let m := (∑ x, W x) / (Fintype.card A : ℝ)
  let V : Fin k → (Fin k → A) → ℝ := fun i x => m - W (x i)
  have hWV : Measurable fun x : A => m - W x := Measurable.of_discrete
  have hInd : iIndepFun V ν :=
    iIndepFun_pi (X := fun _ : Fin k => fun x : A => m - W x) (fun _ => hWV.aemeasurable)
  have hM (i : Fin k) :
      (∫ x : Fin k → A, W (x i) ∂ν) = m := by
    have hp : MeasurePreserving (Function.eval i) ν μ :=
      measurePreserving_eval (fun _ : Fin k => μ) i
    calc
      _ = ∫ z, W z ∂(Measure.map (Function.eval i) ν) :=
        (integral_map hp.measurable.aemeasurable
          (show Measurable W from Measurable.of_discrete).aestronglyMeasurable).symm
      _ = m := by rw [hp.map_eq]; exact integral_uniformFintype W
  let c : ℝ≥0 := (‖B - (0 : ℝ)‖₊ / 2) ^ 2
  have hSub (i : Fin k) (_ : i ∈ (Finset.univ : Finset (Fin k))) :
      HasSubgaussianMGF (V i) c ν := by
    have hMeas : Measurable fun x : Fin k → A => W (x i) :=
      (show Measurable W from Measurable.of_discrete).comp (measurable_pi_apply i)
    have h := hasSubgaussianMGF_of_mem_Icc (μ := ν) hMeas.aemeasurable
      (ae_of_all ν fun x => hW (x i))
    rw [hM i] at h
    simpa [V, c, Pi.neg_def, neg_sub] using h.neg
  have hHoeffding :=
    HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hInd hSub
      (mul_nonneg (Nat.cast_nonneg k) hη)
  have hEvent :
      {x : Fin k → A | (∑ i : Fin k, W (x i)) < (k : ℝ) * (m - η)} ⊆
      {x : Fin k → A | (k : ℝ) * η ≤ ∑ i : Fin k, V i x} := by
    intro x hx
    change (k : ℝ) * η ≤ ∑ i : Fin k, (m - W (x i))
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    change (∑ i : Fin k, W (x i)) < (k : ℝ) * (m - η) at hx
    linarith
  refine (measureReal_mono hEvent).trans (hHoeffding.trans_eq ?_)
  congr 1
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    NNReal.coe_mul, NNReal.coe_natCast, c, NNReal.coe_pow, NNReal.coe_div,
    NNReal.coe_two, sub_zero, coe_nnnorm, Real.norm_eq_abs, abs_of_pos hB, mul_pow]
  have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  field_simp [hB.ne', hk']

variable {α : Type*} [DecidableEq α]

/-- Hoeffding's lower-tail inequality stated in HILL's finite uniform-counting model. -/
theorem finiteIIDLowerTail : FiniteIIDLowerTailStatement (α := α) := by
  intro S W hS B η hB hη hW k hk
  classical
  let A := ↥S
  let : Nonempty A := hS.to_subtype
  let : MeasurableSpace A := ⊤
  let : DiscreteMeasurableSpace A := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  let SS := Fintype.piFinset (fun _ : Fin k => S)
  let e : (Fin k → A) ≃ ↥SS :=
    { toFun := fun x => ⟨fun i => (x i).val, Fintype.mem_piFinset.mpr (fun i => (x i).property)⟩
      invFun := fun x i => ⟨x.val i, Fintype.mem_piFinset.mp x.property i⟩
      left_inv := fun x => rfl
      right_inv := fun x => Subtype.ext rfl }
  have hCard : Fintype.card (Fin k → A) = SS.card :=
    (Fintype.card_congr e).trans (Fintype.card_coe SS)
  let cutoff := (k : ℝ) * (averageOn S W - η)
  let P : (Fin k → α) → Prop := fun xs => (∑ i : Fin k, W (xs i)) < cutoff
  let E : Set (Fin k → A) := {x | P (fun i => (x i).val)}
  have hCardE :
      ((Finset.univ : Finset (Fin k → A)).filter (· ∈ E)).card =
        (SS.filter P).card := by
    refine Finset.card_bij (fun x _ => (e x).val) ?_ ?_ ?_
    · intro x hx
      exact Finset.mem_filter.mpr ⟨(e x).property, (Finset.mem_filter.mp hx).2⟩
    · intro x _ y _ hxy
      exact e.injective (Subtype.ext hxy)
    · intro x hx
      obtain ⟨hxS, hxP⟩ := Finset.mem_filter.mp hx
      have he := e.apply_symm_apply ⟨x, hxS⟩
      refine ⟨e.symm ⟨x, hxS⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩,
        congrArg Subtype.val he⟩
      change P ((e (e.symm ⟨x, hxS⟩)).val)
      rwa [he]
  have hMeasure :
      (PMF.uniformOfFintype (Fin k → A)).toMeasure.real E =
        iidLowerTailOn S W k cutoff := by
    simp only [measureReal_def, PMF.uniformOfFintype]
    rw [PMF.toMeasure_uniformOfFinset_apply _ _ MeasurableSet.of_discrete,
      ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast,
      hCardE, Finset.card_univ, hCard]
    rfl
  have hMean : (∑ x : A, W x.val) / (Fintype.card A : ℝ) = averageOn S W := by
    rw [Fintype.card_coe, Finset.sum_coe_sort]
    rfl
  rw [← hMeasure]
  simpa only [hMean, E, P, cutoff] using
    finiteUniformLowerTail (fun x : A => W x.val) hB hη (fun x => hW x.val x.property) hk

end HILL.PRG.Proposed

end HILL416_Hoeffding

section HILL416_LeftoverHash

open scoped BigOperators

namespace HILL.PRG.Proposed

/- The finite second-moment argument is adapted from Wentao Li's proof of
HILL.PRG.lemma_4_8.
https://prove2.me/theorems/0d655459-ea71-432d-b377-a9a49c03a0ce -/

set_option maxHeartbeats 1000000 in
private lemma finite_hash_bound {α β κ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq κ]
    (X : Finset α) (Y : Finset β) (K : Finset κ) (D : α → ℝ) (h : κ → α → β)
    (hD : ∀ x ∈ X, 0 ≤ D x) (hsum : ∑ x ∈ X, D x = 1)
    (hY : 0 < Y.card) (hK : 0 < K.card)
    (hmap : ∀ k ∈ K, ∀ x ∈ X, h k x ∈ Y)
    (hcoll : ∀ x ∈ X, ∀ x' ∈ X, x ≠ x' →
      (∑ k ∈ K, if h k x = h k x' then (1 : ℝ) else 0) ≤
        (K.card : ℝ) / Y.card) :
    let P := fun k a => ∑ x ∈ X, if h k x = a then D x else 0
    (∑ k ∈ K, ∑ a ∈ Y, |P k a - 1 / (Y.card : ℝ)|) ^ 2 ≤
      (Y.card : ℝ) * (K.card : ℝ) ^ 2 * (∑ x ∈ X, (D x) ^ 2) := by
  classical
  intro P
  let M : ℝ := Y.card
  let N : ℝ := K.card
  let C : ℝ := ∑ x ∈ X, (D x) ^ 2
  have hM : 0 < M := by dsimp [M]; exact_mod_cast hY
  have hN : 0 < N := by dsimp [N]; exact_mod_cast hK
  have hp (k : κ) (hk : k ∈ K) : ∑ a ∈ Y, P k a = 1 := by
    dsimp [P]
    rw [Finset.sum_comm]
    calc
      _ = ∑ x ∈ X, D x := by
        apply Finset.sum_congr rfl
        intro x hx
        simp [hmap k hk x hx, eq_comm]
      _ = 1 := hsum
  have hmoment (k : κ) (hk : k ∈ K) :
      ∑ a ∈ Y, (P k a) ^ 2 =
        ∑ x ∈ X, ∑ x' ∈ X, if h k x = h k x' then D x * D x' else 0 := by
    simp_rw [P, pow_two, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x' hx'
    have hprod (a : β) :
        (if h k x = a then D x else 0) * (if h k x' = a then D x' else 0) =
          if h k x = a then (if h k x' = a then D x * D x' else 0) else 0 := by
      split_ifs <;> simp_all
    simp_rw [hprod]
    simp [hmap k hk x hx, eq_comm]
  have htotal : (∑ k ∈ K, ∑ a ∈ Y, (P k a) ^ 2) ≤ N * C + N / M := by
    calc
      _ = ∑ x ∈ X, ∑ x' ∈ X,
          (D x * D x') * (∑ k ∈ K, if h k x = h k x' then (1 : ℝ) else 0) := by
        simp_rw [Finset.sum_congr rfl (fun k hk => hmoment k hk)]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro x hx
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro x' hx'
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        split_ifs <;> simp
      _ ≤ ∑ x ∈ X, ∑ x' ∈ X,
          (N * (if x = x' then (D x) ^ 2 else 0) + (N / M) * (D x * D x')) := by
        apply Finset.sum_le_sum
        intro x hx
        apply Finset.sum_le_sum
        intro x' hx'
        by_cases hxx : x = x'
        · subst x'
          simp only [ite_true, Finset.sum_const, nsmul_eq_mul, mul_one]
          dsimp only [N]
          nlinarith [mul_nonneg (div_nonneg hN.le hM.le) (sq_nonneg (D x))]
        · rw [if_neg hxx]
          have hh := mul_le_mul_of_nonneg_left (hcoll x hx x' hx' hxx)
            (mul_nonneg (hD x hx) (hD x' hx'))
          simpa only [mul_zero, zero_add, mul_comm] using hh
      _ = N * C + N / M := by
        simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        have hdiag : (∑ x ∈ X, ∑ x' ∈ X, if x = x' then (D x) ^ 2 else 0) = C := by
          apply Finset.sum_congr rfl
          intro x hx
          simp [hx]
        have hall : (∑ x ∈ X, ∑ x' ∈ X, D x * D x') = 1 := by
          rw [← Finset.sum_mul_sum, hsum, one_mul]
        rw [hdiag]; simp only [hsum, mul_one]
  have hvariance (k : κ) (hk : k ∈ K) :
      ∑ a ∈ Y, (P k a - 1 / M) ^ 2 = (∑ a ∈ Y, (P k a) ^ 2) - 1 / M := by
    have heq (a : β) : (P k a - 1 / M) ^ 2 =
        (P k a) ^ 2 - (2 / M) * P k a + (1 / M) ^ 2 := by ring
    simp_rw [heq, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hp k hk, Finset.sum_const, nsmul_eq_mul]
    dsimp only [M]
    field_simp
    ring
  have hv : (∑ k ∈ K, ∑ a ∈ Y, (P k a - 1 / M) ^ 2) ≤ N * C := by
    simp_rw [Finset.sum_congr rfl (fun k hk => hvariance k hk)]
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    have heq : N * (1 / M) = N / M := by ring
    rw [heq]
    linarith
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (K ×ˢ Y)
    (fun z => |P z.1 z.2 - 1 / M|) (fun _ => (1 : ℝ))
  simp only [mul_one, sq_abs, one_pow, Finset.sum_const, nsmul_eq_mul,
    Finset.card_product, Nat.cast_mul, Finset.sum_product] at hcs
  calc
    _ ≤ (∑ k ∈ K, ∑ a ∈ Y, (P k a - 1 / M) ^ 2) * (N * M) := hcs
    _ ≤ (N * C) * (N * M) := mul_le_mul_of_nonneg_right hv (by positivity)
    _ = _ := by ring


private lemma cast_card_filter {τ : Type*} (A : Finset τ) (p : τ → Prop)
    [DecidablePred p] :
    ((A.filter p).card : ℝ) = ∑ x ∈ A, if p x then (1 : ℝ) else 0 := by
  rw [← Finset.sum_filter]
  simp

variable {α β κ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq κ]

/-- Leftover hashing for a finite uniform source and collision-universal keys. -/
theorem flatLeftoverHash : FlatLeftoverHashStatement (α := α) (ζ := β) (κ := κ) := by
  intro S R Z h hS hR hZ hmap hcoll
  obtain ⟨hSpos, hRpos, hZpos⟩ : (0 : ℝ) < S.card ∧
      (0 : ℝ) < R.card ∧ (0 : ℝ) < Z.card :=
    ⟨Nat.cast_pos.mpr (Finset.card_pos.mpr hS),
     Nat.cast_pos.mpr (Finset.card_pos.mpr hR),
     Nat.cast_pos.mpr (Finset.card_pos.mpr hZ)⟩
  have hcoll' (x : α) (hx : x ∈ S) (y : α) (hy : y ∈ S) (hne : x ≠ y) :
      (∑ r ∈ R, if h r x = h r y then (1 : ℝ) else 0) ≤ (R.card : ℝ) / Z.card := by
    rw [← cast_card_filter]
    exact (le_div_iff₀ hZpos).2 (by simpa only [mul_comm] using hcoll x hx y hy hne)
  have hMoment := finite_hash_bound S Z R (fun _ => 1 / (S.card : ℝ)) h
    (fun _ _ => by positivity)
    (by simp [Finset.sum_const, nsmul_eq_mul, hSpos.ne'])
    (Finset.card_pos.mpr hZ) (Finset.card_pos.mpr hR) hmap hcoll'
  have hSquareWeight : (∑ _x ∈ S, (1 / (S.card : ℝ)) ^ 2) = 1 / (S.card : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    field_simp
  let P (r : κ) (z : β) := ∑ x ∈ S, if h r x = z then 1 / (S.card : ℝ) else 0
  have hL1 : (∑ r ∈ R, ∑ z ∈ Z, |P r z - 1 / (Z.card : ℝ)|) ≤
      (R.card : ℝ) * Real.sqrt ((Z.card : ℝ) / S.card) := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).1
    calc
      _ ≤ (Z.card : ℝ) * (R.card : ℝ) ^ 2 * ∑ _x ∈ S, (1 / (S.card : ℝ)) ^ 2 := hMoment
      _ = _ := by rw [hSquareWeight, mul_pow, Real.sq_sqrt (by positivity)]; ring
  have hActual (r : κ) (hr : r ∈ R) (z : β) :
      lawOn (S ×ˢ R) (fun xr => (xr.2, h xr.2 xr.1)) (r, z) =
        P r z / (R.card : ℝ) := by
    unfold lawOn
    have hFilter :
        (S ×ˢ R).filter (fun xr => (xr.2, h xr.2 xr.1) = (r, z)) =
          (S.filter (fun x => h r x = z)) ×ˢ {r} := by
      ext xr
      rcases xr with ⟨x, r'⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_singleton, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨hx, _⟩, rfl, he⟩
        exact ⟨⟨hx, he⟩, rfl⟩
      · rintro ⟨⟨hx, he⟩, rfl⟩
        exact ⟨⟨hx, hr⟩, rfl, he⟩
    rw [hFilter, Finset.card_product, Finset.card_singleton, mul_one,
      Finset.card_product, Nat.cast_mul]
    simp only [P, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    ring
  have hUniform (r : κ) (hr : r ∈ R) (z : β) (hz : z ∈ Z) :
      lawOn (R ×ˢ Z) id (r, z) = 1 / ((Z.card : ℝ) * R.card) := by
    unfold lawOn
    have hFilter : (R ×ˢ Z).filter (fun x => id x = (r, z)) = {(r, z)} := by
      ext p
      simp only [Finset.mem_filter, id_eq, Finset.mem_singleton]
      exact ⟨And.right, fun e => ⟨e.symm ▸ Finset.mem_product.mpr ⟨hr, hz⟩, e⟩⟩
    rw [hFilter, Finset.card_singleton, Nat.cast_one, Finset.card_product, Nat.cast_mul, mul_comm]
  have hAbs (r : κ) (hr : r ∈ R) (z : β) (hz : z ∈ Z) :
      |lawOn (S ×ˢ R) (fun xr => (xr.2, h xr.2 xr.1)) (r, z) -
        lawOn (R ×ˢ Z) id (r, z)| = |P r z - 1 / (Z.card : ℝ)| / (R.card : ℝ) := by
    rw [hActual r hr z, hUniform r hr z hz]
    rw [show P r z / (R.card : ℝ) - 1 / ((Z.card : ℝ) * R.card) =
      (P r z - 1 / (Z.card : ℝ)) / (R.card : ℝ) by ring, abs_div, abs_of_pos hRpos]
  unfold statDistOn
  rw [Finset.sum_product]
  have hSum :
      (∑ r ∈ R, ∑ z ∈ Z,
        |lawOn (S ×ˢ R) (fun xr => (xr.2, h xr.2 xr.1)) (r, z) -
          lawOn (R ×ˢ Z) id (r, z)|) =
        (∑ r ∈ R, ∑ z ∈ Z, |P r z - 1 / (Z.card : ℝ)|) / (R.card : ℝ) := by
    simp only [Finset.sum_div]
    exact Finset.sum_congr rfl fun r hr => Finset.sum_congr rfl fun z hz => hAbs r hr z hz
  rw [hSum]
  calc
    _ ≤ Real.sqrt ((Z.card : ℝ) / S.card) / 2 :=
      div_le_div_of_nonneg_right
        ((div_le_iff₀ hRpos).2 (by simpa only [mul_comm] using hL1)) (by norm_num)
    _ = _ := by ring

end HILL.PRG.Proposed

end HILL416_LeftoverHash

section HILL416_ConditionalHash

open scoped BigOperators

namespace HILL.PRG.Proposed

variable {α β κ ζ : Type*} [DecidableEq β] [DecidableEq κ] [DecidableEq ζ]

private theorem actualOnFiber (S : Finset α) (R : Finset κ) (f : α → β)
    (h : κ → α → ζ) (hR : R.Nonempty) {y : β} (hy : y ∈ S.image f) (r : κ) (z : ζ) :
    hashActualOn S R f h (y, (r, z)) =
      lawOn S f y *
        lawOn ((S.filter (fun x => f x = y)) ×ˢ R) (fun xr => (xr.2, h xr.2 xr.1)) (r, z) := by
  unfold hashActualOn lawOn
  have hFilter :
      (S ×ˢ R).filter (fun xr => (f xr.1, (xr.2, h xr.2 xr.1)) = (y, (r, z))) =
        ((S.filter (fun x => f x = y)) ×ˢ R).filter (fun xr => (xr.2, h xr.2 xr.1) = (r, z)) := by
    ext xr
    simp only [Finset.mem_filter, Finset.mem_product, Prod.mk.injEq]
    tauto
  rw [hFilter]
  simp only [Finset.card_product, Nat.cast_mul]
  have hFc : ((S.filter (fun x => f x = y)).card : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr ((Finset.fiber_card_ne_zero_iff_mem_image S f y).2 hy)
  have hSc : (S.card : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Finset.card_ne_zero_of_mem (Finset.mem_image.mp hy).choose_spec.1)
  have hRc : (R.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hR.card_ne_zero
  field_simp [hFc, hSc, hRc]

private theorem idealOnFiber (S : Finset α) (R : Finset κ) (Z : Finset ζ) (f : α → β)
    {r : κ} (hr : r ∈ R) {z : ζ} (hz : z ∈ Z) (y : β) :
    hashIdealOn S R Z f (y, (r, z)) =
      lawOn S f y * lawOn (R ×ˢ Z) id (r, z) := by
  unfold hashIdealOn lawOn
  have hFilter :
      ((S ×ˢ R) ×ˢ Z).filter (fun xrz => (f xrz.1.1, (xrz.1.2, xrz.2)) = (y, (r, z))) =
        ((S.filter (fun x => f x = y)) ×ˢ {r}) ×ˢ {z} := by
    ext p
    rcases p with ⟨⟨x, r'⟩, z'⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨⟨hx, _⟩, _⟩, he, hr', hz'⟩
      exact ⟨⟨⟨hx, he⟩, hr'⟩, hz'⟩
    · rintro ⟨⟨⟨hx, he⟩, rfl⟩, rfl⟩
      exact ⟨⟨⟨hx, hr⟩, hz⟩, he, rfl, rfl⟩
  have hUniform : (R ×ˢ Z).filter (fun p => id p = (r, z)) = {(r, z)} := by
    ext p
    simp only [Finset.mem_filter, id_eq, Finset.mem_singleton]
    exact ⟨And.right, fun e => ⟨e.symm ▸ Finset.mem_product.mpr ⟨hr, hz⟩, e⟩⟩
  rw [hFilter, hUniform]
  simp only [Finset.card_product, Finset.card_singleton, mul_one, Nat.cast_mul, Nat.cast_one]
  ring

/-- Retaining the output label makes joint variation distance a weighted sum
of the variation distances on the individual fibers. -/
theorem conditionalHashDistance_eq (S : Finset α) (R : Finset κ) (Z : Finset ζ)
    (f : α → β) (h : κ → α → ζ) (hR : R.Nonempty) :
    statDistOn (hashSupportOn S R Z f) (hashActualOn S R f h) (hashIdealOn S R Z f) =
      ∑ y ∈ S.image f, lawOn S f y *
        statDistOn (R ×ˢ Z)
          (lawOn ((S.filter (fun x => f x = y)) ×ˢ R) (fun xr => (xr.2, h xr.2 xr.1)))
          (lawOn (R ×ˢ Z) id) := by
  unfold statDistOn hashSupportOn
  rw [Finset.sum_product, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro y hy
  rw [← mul_div_assoc, Finset.mul_sum]
  apply congrArg (fun x : ℝ => x / 2)
  refine Finset.sum_congr rfl ?_
  rintro ⟨r, z⟩ hrz
  rw [actualOnFiber S R f h hR hy r z,
    idealOnFiber S R Z f (Finset.mem_product.mp hrz).1 (Finset.mem_product.mp hrz).2 y,
    ← mul_sub, abs_mul, abs_of_nonneg
      (show 0 ≤ lawOn S f y from div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]

private theorem lawOn_isProbOn {A B : Type*} [DecidableEq B] (S : Finset A) (Z : Finset B)
    (f : A → B) (hS : S.Nonempty) (hZ : ∀ x ∈ S, f x ∈ Z) :
    IsProbOn Z (lawOn S f) := by
  refine ⟨fun _ _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _), ?_⟩
  have hS0 : (S.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hS.card_ne_zero
  simp only [lawOn, ← Finset.sum_div, ← Nat.cast_sum,
    ← Finset.card_eq_sum_card_fiberwise hZ, div_self hS0]

private theorem statDist_le_one {A : Type*} [DecidableEq A] (S : Finset A) (D E : A → ℝ)
    (hD : IsProbOn S D) (hE : IsProbOn S E) :
    statDistOn S D E ≤ 1 := by
  unfold statDistOn
  calc
    _ ≤ (∑ x ∈ S, (D x + E x)) / 2 :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum fun x hx => by
        simpa only [sub_eq_add_neg, abs_neg, abs_of_nonneg (hD.1 x hx),
          abs_of_nonneg (hE.1 x hx)] using abs_add_le (D x) (-E x)) (by norm_num)
    _ = 1 := by rw [Finset.sum_add_distrib, hD.2, hE.2]; norm_num

private theorem smallFiberProb_eq_sum {A B : Type*} [DecidableEq A] [DecidableEq B]
    (S : Finset A) (f : A → B) (L : ℝ) :
    smallFiberProb S f L =
      ∑ y ∈ S.image f, lawOn S f y * (if (fiberCardOn S f y : ℝ) < L then 1 else 0) := by
  classical
  unfold smallFiberProb uniformProb
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
  simp only [Nat.cast_one]
  rw [← Finset.sum_fiberwise_of_maps_to' (fun x hx => Finset.mem_image_of_mem f hx)
    (fun y => if (fiberCardOn S f y : ℝ) < L then (1 : ℝ) else 0), Finset.sum_div]
  exact Finset.sum_congr rfl fun y _ => by
    simp only [Finset.sum_const, nsmul_eq_mul, lawOn, div_mul_eq_mul_div]

variable [DecidableEq α]

/-- Conditional leftover hashing for the flat fibers of a deterministic map. -/
theorem flatConditionalHash :
    FlatConditionalHashStatement (α := α) (β := β) (κ := κ) (ζ := ζ) := by
  intro S R Z f h hS hR hZ hmap hcoll L hL
  rw [conditionalHashDistance_eq S R Z f h hR]
  let C := (1 / 2 : ℝ) * Real.sqrt ((Z.card : ℝ) / L)
  have hFiber (y : β) (hy : y ∈ S.image f) :
      statDistOn (R ×ˢ Z)
        (lawOn ((S.filter (fun x => f x = y)) ×ˢ R) (fun xr => (xr.2, h xr.2 xr.1)))
        (lawOn (R ×ˢ Z) id) ≤
      (if (fiberCardOn S f y : ℝ) < L then 1 else 0) + C := by
    let T := S.filter (fun x => f x = y)
    have hT : T.Nonempty :=
      Finset.card_ne_zero.mp ((Finset.fiber_card_ne_zero_iff_mem_image S f y).mpr hy)
    have hTmap : ∀ r ∈ R, ∀ x ∈ T, h r x ∈ Z :=
      fun r hr x hx => hmap r hr x (Finset.mem_filter.mp hx).1
    change statDistOn (R ×ˢ Z)
      (lawOn (T ×ˢ R) (fun xr => (xr.2, h xr.2 xr.1))) (lawOn (R ×ˢ Z) id) ≤
        (if (T.card : ℝ) < L then 1 else 0) + C
    split_ifs with hSmall
    · exact (statDist_le_one (R ×ˢ Z)
          (lawOn (T ×ˢ R) (fun xr => (xr.2, h xr.2 xr.1))) (lawOn (R ×ˢ Z) id)
          (lawOn_isProbOn _ _ _ (hT.product hR) (fun p hp =>
            let hm := Finset.mem_product.mp hp
            Finset.mem_product.mpr ⟨hm.2, hTmap p.2 hm.2 p.1 hm.1⟩))
          (lawOn_isProbOn _ _ _ (hR.product hZ) (fun _ hp => hp))).trans
          (le_add_of_nonneg_right (by dsimp [C]; positivity))
    · calc
        _ ≤ (1 / 2 : ℝ) * Real.sqrt ((Z.card : ℝ) / T.card) :=
          flatLeftoverHash T R Z h hT hR hZ hTmap (fun x hx x' hx' hne =>
            hcoll x (Finset.mem_filter.mp hx).1 x' (Finset.mem_filter.mp hx').1 hne)
        _ ≤ _ := by
          simpa only [zero_add, C] using mul_le_mul_of_nonneg_left
            (Real.sqrt_le_sqrt
              (div_le_div_of_nonneg_left (Nat.cast_nonneg (α := ℝ) Z.card) hL
                (le_of_not_gt hSmall))) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  calc
    _ ≤ ∑ y ∈ S.image f, lawOn S f y *
        ((if (fiberCardOn S f y : ℝ) < L then 1 else 0) + C) :=
      Finset.sum_le_sum fun y hy => mul_le_mul_of_nonneg_left (hFiber y hy)
        (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    _ = _ := by
      simp_rw [mul_add, Finset.sum_add_distrib]
      rw [← smallFiberProb_eq_sum S f L, ← Finset.sum_mul,
        (lawOn_isProbOn S (S.image f) f hS (fun _ hx => Finset.mem_image_of_mem f hx)).2,
        one_mul]

end HILL.PRG.Proposed

end HILL416_ConditionalHash

section HILL416_RepeatedExtraction

namespace HILL.PRG.Proposed

open scoped BigOperators

theorem cube_card (T : ℕ) : (cube T).card = 2 ^ T := by
  unfold cube Levin2003.cube
  rw [Finset.card_image_of_injective _ List.ofFn_injective]
  simp

theorem cube_nonempty (T : ℕ) : (cube T).Nonempty :=
  Finset.card_pos.mp (by rw [cube_card]; positivity)

variable {α β κ ζ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq κ] [DecidableEq ζ]

theorem flatConditionalHashBits :
    FlatConditionalHashBitsStatement (α := α) (β := β) (κ := κ) (ζ := ζ) := by
  intro S R Z f h hS hR hZ hMap hColl j m hZcard δ hBad
  have hBound := flatConditionalHash S R Z f h hS hR hZ hMap hColl
    ((2 : ℝ) ^ (j + 2 * m)) (by positivity)
  have hRatio : (Z.card : ℝ) / (2 : ℝ) ^ (j + 2 * m) =
      (1 / (2 : ℝ) ^ m) ^ 2 := by
    rw [hZcard, Nat.cast_pow, Nat.cast_ofNat, pow_add, Nat.mul_comm 2 m, pow_mul, div_pow]
    field_simp
  rw [hRatio, Real.sqrt_sq (by positivity), show
    (1 / 2 : ℝ) * (1 / 2 ^ m) = 1 / 2 ^ (m + 1) by rw [pow_succ]; ring] at hBound
  exact hBound.trans (add_le_add_left hBad _)

omit [DecidableEq α] in
private theorem hashDistance_singleton (S : Finset α) (R : Finset κ) (z : ζ)
    (f : α → β) (h : κ → α → ζ) (hMap : ∀ r ∈ R, ∀ x ∈ S, h r x ∈ ({z} : Finset ζ)) :
    statDistOn (hashSupportOn S R {z} f)
      (hashActualOn S R f h) (hashIdealOn S R {z} f) = 0 := by
  have hLaw (p : β × (κ × ζ)) :
      hashActualOn S R f h p = hashIdealOn S R {z} f p := by
    unfold hashActualOn hashIdealOn lawOn
    have hFilter :
        ((S ×ˢ R) ×ˢ {z}).filter
          (fun xrz => (f xrz.1.1, (xrz.1.2, xrz.2)) = p) =
        ((S ×ˢ R).filter (fun xr => (f xr.1, (xr.2, h xr.2 xr.1)) = p)) ×ˢ {z} := by
      ext ⟨⟨x, r⟩, w⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨⟨hx, hr⟩, rfl⟩, hp⟩
        exact ⟨⟨⟨hx, hr⟩, (Finset.mem_singleton.mp (hMap r hr x hx)) ▸ hp⟩, rfl⟩
      · rintro ⟨⟨⟨hx, hr⟩, hp⟩, rfl⟩
        exact ⟨⟨⟨hx, hr⟩, rfl⟩, (Finset.mem_singleton.mp (hMap r hr x hx)) ▸ hp⟩
    rw [hFilter]
    simp
  simp [statDistOn, hLaw]

omit [DecidableEq α] in
private theorem logFiber_repeat {k : ℕ} (S : Finset α) (f : α → β)
    (xs : Fin k → α) (hxs : xs ∈ Fintype.piFinset (fun _ : Fin k => S)) :
    logFiberOn (Fintype.piFinset (fun _ : Fin k => S)) (repeatEval f) xs =
      ∑ i : Fin k, logFiberOn S f (xs i) := by
  unfold logFiberOn repeatEval
  rw [productFiber S f, Nat.cast_prod, Real.logb_prod]
  intro i _
  exact Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr ⟨xs i,
    Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mp hxs i, rfl⟩⟩)

/-- Concentration on the product seed space, followed by conditional leftover hashing. -/
theorem repeatedUniformExtraction :
    RepeatedUniformExtractionStatement (κ := κ) := by
  intro T k j m f R h s hk hR hs hj hmargin
  dsimp only
  intro hMap hColl
  classical
  let S := Fintype.piFinset (fun _ : Fin k => cube T)
  have hS : S.Nonempty := by
    obtain ⟨x, hx⟩ := cube_nonempty T
    exact ⟨fun _ => x, Fintype.mem_piFinset.mpr (fun _ => hx)⟩
  by_cases hz : j = 0
  · have hCube : cube 0 = {[]} := by
      unfold cube Levin2003.cube
      ext x
      simp
    rw [hz, hCube] at hMap ⊢
    rw [hashDistance_singleton S R [] (repeatEval f) h hMap]
    positivity
  have hPos : 0 ≤ (k : ℝ) * ((T : ℝ) - entropyOf (cube T) f - s / 2) :=
    le_of_not_gt fun hNeg => hz (hj.trans (Nat.floor_of_nonpos hNeg.le))
  have hBudget : (j : ℝ) ≤ (k : ℝ) * ((T : ℝ) - entropyOf (cube T) f - s / 2) := by
    rw [hj]
    exact Nat.floor_le hPos
  have hLogCard : Real.logb 2 ((cube T).card : ℝ) = (T : ℝ) := by
    rw [cube_card, Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
    exact mul_one _
  have hRange (x : Bits) (hx : x ∈ cube T) :
      0 ≤ logFiberOn (cube T) f x ∧ logFiberOn (cube T) f x ≤ (T : ℝ) + 1 := by
    obtain ⟨hlo, hhi⟩ := logFiberBounds (cube T) f x hx
    rw [hLogCard] at hhi
    exact ⟨hlo, by linarith⟩
  have hMean : averageOn (cube T) (logFiberOn (cube T) f) =
      (T : ℝ) - entropyOf (cube T) f := by
    rw [meanLogFiber _ _ (cube_nonempty T), hLogCard]
  let cutoff := (k : ℝ) * (averageOn (cube T) (logFiberOn (cube T) f) - s / 4)
  have hCutoff : (j : ℝ) + 2 * (m : ℝ) ≤ cutoff := by
    dsimp [cutoff]
    rw [hMean]
    linarith
  have hBad :
      smallFiberProb S (repeatEval f) ((2 : ℝ) ^ (j + 2 * m)) ≤
        iidLowerTailOn (cube T) (logFiberOn (cube T) f) k cutoff := by
    unfold smallFiberProb iidLowerTailOn uniformProb
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro xs hxs
    obtain ⟨hx, hf⟩ := Finset.mem_filter.mp hxs
    have hFiber : (0 : ℝ) < (fiberCardOn S (repeatEval f) (repeatEval f xs) : ℝ) :=
      Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨xs, Finset.mem_filter.mpr ⟨hx, rfl⟩⟩)
    have hLog := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2) hFiber hf
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one, Nat.cast_add,
      Nat.cast_mul, Nat.cast_ofNat] at hLog
    change logFiberOn S (repeatEval f) xs < _ at hLog
    rw [logFiber_repeat (cube T) f xs hx] at hLog
    exact Finset.mem_filter.mpr ⟨hx, hLog.trans_le hCutoff⟩
  have hH := finiteIIDLowerTail (cube T) (logFiberOn (cube T) f) (cube_nonempty T)
    ((T : ℝ) + 1) (s / 4) (by positivity) (by positivity) hRange k hk
  have hExponent : -(2 * (k : ℝ) * (s / 4) ^ 2) / ((T : ℝ) + 1) ^ 2 =
      -((k : ℝ) * s ^ 2) / (8 * ((T : ℝ) + 1) ^ 2) := by
    field_simp
    ring
  rw [hExponent] at hH
  exact flatConditionalHashBits S R (cube j) (repeatEval f) h hS hR (cube_nonempty j)
    hMap hColl j m (cube_card j) _ (hBad.trans hH)

end HILL.PRG.Proposed

end HILL416_RepeatedExtraction

section HILL416_FiniteLaws

namespace HILL.PRG

open scoped BigOperators

section Reindex

variable {A B C : Type*}

theorem finset_card_eq_of_bijOn {f : A → B} {S : Finset A} {T : Finset B}
    (h : Set.BijOn f ↑S ↑T) : S.card = T.card :=
  Finset.card_bij (fun x _ => f x) h.mapsTo h.injOn (fun _ hb => by
    obtain ⟨x, hx, he⟩ := h.surjOn hb
    exact ⟨x, hx, he⟩)

/-- A bijection of finite seed sets preserves all image probabilities. -/
theorem lawOn_eq_of_bijOn [DecidableEq C] {f : A → B} {S : Finset A} {T : Finset B}
    (h : Set.BijOn f ↑S ↑T) (g : B → C) :
    lawOn S (g ∘ f) = lawOn T g := by
  funext y
  unfold lawOn
  rw [finset_card_eq_of_bijOn h]
  congr 2
  apply finset_card_eq_of_bijOn (f := f)
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨hxS, hxG⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨h.mapsTo hxS, hxG⟩
  · intro x hx y hy hxy
    exact h.injOn (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1 hxy
  · intro x hx
    obtain ⟨hxT, hxG⟩ := Finset.mem_filter.mp hx
    obtain ⟨y, hy, rfl⟩ := h.surjOn hxT
    exact ⟨y, Finset.mem_filter.mpr ⟨hy, hxG⟩, rfl⟩

theorem entropyOf_eq_of_bijOn [DecidableEq C] {f : A → B} {S : Finset A} {T : Finset B}
    (h : Set.BijOn f ↑S ↑T) (g : B → C) :
    entropyOf S (g ∘ f) = entropyOf T g := by
  unfold entropyOf
  rw [lawOn_eq_of_bijOn h g]
  congr 1
  ext z
  simp only [Finset.mem_image, Function.comp_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨f x, h.mapsTo hx, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨x, hx, rfl⟩ := h.surjOn hy
    exact ⟨x, hx, rfl⟩

theorem entropyOf_injective_map [DecidableEq B] [DecidableEq C] (S : Finset A) (f : A → B)
    (g : B → C) (h : Set.InjOn g ↑(S.image f)) :
    entropyOf S (g ∘ f) = entropyOf S f := by
  classical
  unfold entropyOf shannonOn
  rw [← Finset.image_image, Finset.sum_image h]
  apply Finset.sum_congr rfl
  intro y hy
  have hFilter : S.filter (fun x => (g ∘ f) x = g y) = S.filter (fun x => f x = y) := by
    ext x
    simp only [Finset.mem_filter, Function.comp_apply]
    exact and_congr_right (fun hx => h.eq_iff (Finset.mem_image_of_mem f hx) hy)
  simp only [lawOn, hFilter]

/-- Appending two fixed-width words gives a bijection with the longer cube. -/
theorem append_bijOn (L R : ℕ) :
    Set.BijOn (fun p : Bits × Bits => p.1 ++ p.2) ↑(cube L ×ˢ cube R) ↑(cube (L + R)) := by
  constructor
  · intro p hp
    obtain ⟨h₁, h₂⟩ := Finset.mem_product.mp hp
    simp [mem_cube_iff_length, mem_cube_iff_length.mp h₁, mem_cube_iff_length.mp h₂]
  constructor
  · intro p hp q hq he
    have hpL := mem_cube_iff_length.mp (Finset.mem_product.mp hp).1
    have hqL := mem_cube_iff_length.mp (Finset.mem_product.mp hq).1
    exact Prod.ext (by simpa only [List.take_left' hpL, List.take_left' hqL] using
        (congrArg (List.take L) he))
      (by simpa only [List.drop_left' hpL, List.drop_left' hqL] using (congrArg (List.drop L) he))
  · intro x hx
    have hxlen := mem_cube_iff_length.mp hx
    exact ⟨(x.take L, x.drop L), Finset.mem_product.mpr
      ⟨mem_cube_iff_length.mpr (by simp [hxlen]), mem_cube_iff_length.mpr (by simp [hxlen])⟩,
      List.take_append_drop L x⟩

end Reindex

namespace Proposed

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

private theorem coordinate_average (S : Finset α) (W : α → ℝ)
    (hS : S.Nonempty) {k : ℕ} (i : Fin k) :
    averageOn (Fintype.piFinset (fun _ : Fin k => S)) (fun xs => W (xs i)) =
      averageOn S W := by
  let Q := Fintype.piFinset (fun _ : Fin k => S)
  have hCard : (Q.card : ℝ) = (S.card : ℝ) ^ k := by
    rw [Fintype.card_piFinset_const, Nat.cast_pow]
  have hPowSum : (∑ xs ∈ Q, W (xs i)) = (S.card : ℝ) ^ (k - 1) * ∑ x ∈ S, W x := by
    rw [← Finset.sum_fiberwise_of_maps_to'
      (fun xs (hx : xs ∈ Q) => Fintype.mem_piFinset.mp hx i) W, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [Fintype.card_filter_piFinset_const_eq_of_mem S i hx, Fintype.card_fin, Nat.cast_pow]
  unfold averageOn
  rw [hCard, hPowSum]
  have hk : k - 1 + 1 = k := Nat.sub_add_cancel (Nat.zero_lt_of_lt i.isLt)
  have hp := pow_succ (S.card : ℝ) (k - 1)
  rw [hk] at hp
  rw [hp, mul_div_mul_left _ _ (pow_pos (by exact_mod_cast hS.card_pos) _).ne']

theorem productEntropy : ProductEntropyStatement (α := α) (β := β) := by
  intro S f hS k
  let Q := Fintype.piFinset (fun _ : Fin k => S)
  have hQ : Q.Nonempty := by
    obtain ⟨x, hx⟩ := hS
    exact ⟨fun _ => x, Fintype.mem_piFinset.mpr (fun _ => hx)⟩
  have hFiber (xs : Fin k → α) (hxs : xs ∈ Q) :
      logFiberOn Q (repeatEval f) xs = ∑ i : Fin k, logFiberOn S f (xs i) := by
    unfold logFiberOn repeatEval
    rw [productFiber S f, Nat.cast_prod, Real.logb_prod]
    exact fun i _ => Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr ⟨xs i,
      Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mp hxs i, rfl⟩⟩)
  have hAvg :
      averageOn Q (logFiberOn Q (repeatEval f)) =
        (k : ℝ) * averageOn S (logFiberOn S f) := by
    unfold averageOn
    rw [Finset.sum_congr rfl hFiber, Finset.sum_comm, Finset.sum_div]
    change (∑ i : Fin k, averageOn Q (fun xs => logFiberOn S f (xs i))) =
      (k : ℝ) * averageOn S (logFiberOn S f)
    calc
      _ = ∑ _ : Fin k, averageOn S (logFiberOn S f) :=
        Finset.sum_congr rfl (fun i _ => coordinate_average S _ hS i)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [meanLogFiber Q _ hQ, meanLogFiber S f hS] at hAvg
  have hLog : Real.logb 2 (Q.card : ℝ) = (k : ℝ) * Real.logb 2 (S.card : ℝ) := by
    rw [Fintype.card_piFinset_const, Nat.cast_pow, Real.logb_pow]
  change entropyOf Q (repeatEval f) = _
  rw [hLog] at hAvg
  linarith

end Proposed
end HILL.PRG

end HILL416_FiniteLaws

section HILL416_IdealEntropy

namespace HILL.PRG

open scoped BigOperators

private theorem entropyTerm_mul (p q : ℝ) :
    -((p * q) * Real.logb 2 (p * q)) =
      -(p * Real.logb 2 p) * q + p * -(q * Real.logb 2 q) := by
  by_cases hp : p = 0
  · simp [hp]
  · by_cases hq : q = 0
    · simp [hq]
    · rw [Real.logb_mul hp hq]
      ring

private theorem shannonOn_product {α β : Type*} (s : Finset α) (t : Finset β)
    (D : α → ℝ) (E : β → ℝ)
    (hD : ∑ x ∈ s, D x = 1) (hE : ∑ y ∈ t, E y = 1) :
    shannonOn (s ×ˢ t) (fun z => D z.1 * E z.2) = shannonOn s D + shannonOn t E := by
  rw [shannonOn, Finset.sum_product]
  simp_rw [entropyTerm_mul, Finset.sum_add_distrib, ← Finset.mul_sum, hE, mul_one]
  rw [← Finset.sum_mul, hD, one_mul]
  rfl

theorem lawOn_product {A B C D : Type*} [DecidableEq C] [DecidableEq D]
    (S : Finset A) (T : Finset B) (f : A → C) (g : B → D) (z : C × D) :
    lawOn (S ×ˢ T) (fun p => (f p.1, g p.2)) z =
      lawOn S f z.1 * lawOn T g z.2 := by
  rcases z with ⟨b, d⟩
  unfold lawOn
  have hFilter : ((S ×ˢ T).filter (fun p => (f p.1, g p.2) = (b, d))) =
      S.filter (fun x => f x = b) ×ˢ T.filter (fun y => g y = d) := by
    ext ⟨x, y⟩
    simp only [Finset.mem_filter, Finset.mem_product, Prod.mk.injEq]
    tauto
  rw [hFilter]
  simp only [Finset.card_product, Nat.cast_mul, div_mul_div_comm]

private theorem sum_lawOn_image {A B : Type*} [DecidableEq B]
    (S : Finset A) (hS : S.Nonempty) (f : A → B) :
    ∑ y ∈ S.image f, lawOn S f y = 1 := by
  simp only [lawOn, ← Finset.sum_div, ← Nat.cast_sum, ← Finset.card_eq_sum_card_image,
    div_self (Nat.cast_ne_zero.mpr hS.card_ne_zero : (S.card : ℝ) ≠ 0)]

theorem entropyOf_product {A B C D : Type*} [DecidableEq C] [DecidableEq D]
    (S : Finset A) (T : Finset B) (hS : S.Nonempty) (hT : T.Nonempty)
    (f : A → C) (g : B → D) :
    entropyOf (S ×ˢ T) (fun p => (f p.1, g p.2)) = entropyOf S f + entropyOf T g := by
  have hImage : (S ×ˢ T).image (fun p => (f p.1, g p.2)) = S.image f ×ˢ T.image g := by
    ext ⟨y, z⟩
    simp only [Finset.mem_image, Finset.mem_product, Prod.exists, Prod.mk.injEq]
    constructor
    · rintro ⟨x, w, ⟨hx, hw⟩, hy, hz⟩
      exact ⟨⟨x, hx, hy⟩, ⟨w, hw, hz⟩⟩
    · rintro ⟨⟨x, hx, hy⟩, ⟨w, hw, hz⟩⟩
      exact ⟨x, w, ⟨hx, hw⟩, hy, hz⟩
  rw [entropyOf, hImage, show lawOn (S ×ˢ T) (fun p => (f p.1, g p.2)) =
    fun z => lawOn S f z.1 * lawOn T g z.2 from funext (lawOn_product S T f g)]
  exact shannonOn_product _ _ _ _ (sum_lawOn_image S hS f) (sum_lawOn_image T hT g)

private theorem entropyOf_pureProductFirst {A B C : Type*} [DecidableEq C]
    (S : Finset A) (T : Finset B) (hf : T.Nonempty) (f : A → C) :
    entropyOf (S ×ˢ T) (fun p => f p.1) = entropyOf S f := by
  have hImage : (S ×ˢ T).image (fun p => f p.1) = S.image f := by
    ext y
    obtain ⟨z, hz⟩ := hf
    simp only [Finset.mem_image, Finset.mem_product, Prod.exists]
    constructor
    · rintro ⟨x, _, ⟨hx, _⟩, he⟩
      exact ⟨x, hx, he⟩
    · rintro ⟨x, hx, he⟩
      exact ⟨x, z, ⟨hx, hz⟩, he⟩
  unfold entropyOf shannonOn
  rw [hImage]
  apply Finset.sum_congr rfl
  intro y _
  have hFilter : (S ×ˢ T).filter (fun p => f p.1 = y) =
      S.filter (fun x => f x = y) ×ˢ T := by
    ext ⟨x, z⟩
    simp only [Finset.mem_filter, Finset.mem_product]
    tauto
  simp only [lawOn, hFilter, Finset.card_product, Nat.cast_mul,
    mul_div_mul_right _ _ (Nat.cast_ne_zero.mpr hf.card_ne_zero : (T.card : ℝ) ≠ 0)]

private theorem entropyOf_uniformCube (n : ℕ) :
    entropyOf (cube n) id = (n : ℝ) := by
  have hlog (x : Bits) (hx : x ∈ cube n) :
      Proposed.logFiberOn (cube n) id x = 0 := by
    have hFilt : (cube n).filter (fun z => z = x) = {x} := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_singleton]
      exact ⟨And.right, fun h => ⟨h ▸ hx, h⟩⟩
    simp only [Proposed.logFiberOn, Proposed.fiberCardOn, id_eq, hFilt,
      Finset.card_singleton, Nat.cast_one, Real.logb_one]
  have h := Proposed.meanLogFiber (cube n) id (Proposed.cube_nonempty n)
  unfold Proposed.averageOn at h
  rw [Finset.sum_eq_zero hlog, zero_div] at h
  rw [← sub_eq_zero.mp h.symm]
  rw [Proposed.cube_card, Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow,
    Real.logb_self_eq_one (by norm_num), mul_one]

private theorem entropyOf_congr {A B : Type*} [DecidableEq B]
    (S : Finset A) {f g : A → B} (h : Set.EqOn f g ↑S) :
    entropyOf S f = entropyOf S g := by
  unfold entropyOf
  rw [Finset.image_congr h]
  congr 1
  funext y
  unfold lawOn
  have hFilter : S.filter (fun x => f x = y) = S.filter (fun x => g x = y) :=
    Finset.ext (fun x => by
      simp only [Finset.mem_filter]
      exact and_congr_right (fun hx => by rw [h hx]))
  rw [hFilter]

private theorem entropyOf_cubePrefix {j N : ℕ} (hj : j ≤ N) :
    entropyOf (cube N) (List.take j) = (j : ℝ) := by
  have h := entropyOf_eq_of_bijOn (append_bijOn j (N - j)) (List.take j)
  have hSum : j + (N - j) = N := by omega
  rw [hSum] at h
  rw [← h, ← entropyOf_uniformCube j, ← entropyOf_pureProductFirst (cube j) (cube (N-j))
    (Proposed.cube_nonempty (N-j)) id]
  let S := cube j ×ˢ cube (N - j)
  have hEq : Set.EqOn (List.take j ∘ fun p : Bits × Bits => p.1 ++ p.2)
      (fun p => p.1) ↑S := by
    intro p hp
    exact List.take_left' (mem_cube_iff_length.mp (Finset.mem_product.mp hp).1)
  exact entropyOf_congr S hEq

private theorem range_eq_ofFn (k : ℕ) :
    List.range k = List.ofFn (fun i : Fin k => i.val) := by
  apply List.ext_getElem
  · simp
  · intro i hi h'i
    simp

theorem repeatEval_flatten (F : FunEns) (a k : ℕ → ℕ) (n : ℕ)
    (x : Fin (k n) → Bits) (hx : ∀ i, (x i).length = F.t n) :
    HybridContracts.repeatEval F k (a n) n (Blocks.flatten x) =
      Blocks.flatten (fun i => F.f (a n) n (x i)) := by
  unfold HybridContracts.repeatEval
  rw [range_eq_ofFn, List.flatMap_def, List.map_ofFn]
  unfold Blocks.flatten
  congr 2
  funext i
  exact congrArg (F.f (a n) n) (Blocks.block_flatten x hx i)

theorem repeatEval_length (F : FunEns) (a k : ℕ → ℕ) (n : ℕ)
    (hLen : ∀ x ∈ cube (F.t n), (F.f (a n) n x).length = F.ℓ n)
    (x : Bits) (hx : x ∈ cube (k n * F.t n)) :
    (HybridContracts.repeatEval F k (a n) n x).length = k n * F.ℓ n := by
  have hlen := mem_cube_iff_length.mp hx
  rw [← Blocks.flatten_block hlen, repeatEval_flatten F a k n _
    (Blocks.block_length hlen)]
  exact Blocks.flatten_length _ (fun i => hLen _ (mem_cube_iff_length.mpr (Blocks.block_length hlen i)))

private theorem entropyOf_repeat (F : FunEns) (a k : ℕ → ℕ) (n : ℕ)
    (hLen : ∀ x ∈ cube (F.t n), (F.f (a n) n x).length = F.ℓ n) :
    entropyOf (cube (k n * F.t n)) (HybridContracts.repeatEval F k (a n) n) =
      (k n : ℝ) * shannonOn (cube (F.ℓ n)) (F.law a n) := by
  rw [← entropyOf_eq_of_bijOn (Blocks.flatten_bijOn (k n) (F.t n))]
  let Q := Fintype.piFinset (fun _ : Fin (k n) => cube (F.t n))
  let f := Proposed.repeatEval (F.f (a n) n) (k := k n)
  have hEq : Set.EqOn (HybridContracts.repeatEval F k (a n) n ∘ Blocks.flatten)
      (Blocks.flatten ∘ f) ↑Q := by
    intro x hx
    exact repeatEval_flatten F a k n x (fun i =>
      mem_cube_iff_length.mp (Fintype.mem_piFinset.mp hx i))
  have hInjective : Set.InjOn (Blocks.flatten (k := k n)) (↑(Q.image f) : Set (Fin (k n) → Bits)) := by
    apply (Blocks.flatten_bijOn (k n) (F.ℓ n)).injOn.mono
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact Fintype.mem_piFinset.mpr (fun i =>
      mem_cube_iff_length.mpr (hLen _ (Fintype.mem_piFinset.mp hx i)))
  rw [entropyOf_congr Q hEq, entropyOf_injective_map Q f Blocks.flatten hInjective]
  have hp := Proposed.productEntropy (cube (F.t n)) (F.f (a n) n) (Proposed.cube_nonempty _) (k n)
  change entropyOf Q f = _ at hp
  rw [hp, Proposed.entropyOfOnSuperset _ (cube (F.ℓ n)) _
    (fun x hx => mem_cube_iff_length.mpr (hLen x hx))]
  rfl

theorem append_three_bijOn (A B C : ℕ) :
    Set.BijOn (fun q : (Bits × Bits) × Bits => q.1.1 ++ q.1.2 ++ q.2)
      ↑((cube A ×ˢ cube B) ×ˢ cube C) ↑(cube (A + B + C)) := by
  have h₁ := append_bijOn A B
  have h₂ := append_bijOn (A + B) C
  have h : Set.BijOn (fun q : (Bits × Bits) × Bits => (q.1.1 ++ q.1.2, q.2))
      ↑((cube A ×ˢ cube B) ×ˢ cube C) ↑(cube (A + B) ×ˢ cube C) := by
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      exact Finset.mem_product.mpr ⟨h₁.mapsTo (Finset.mem_product.mp hx).1,
        (Finset.mem_product.mp hx).2⟩
    · intro x hx y hy he
      exact Prod.ext (h₁.injOn (Finset.mem_product.mp hx).1 (Finset.mem_product.mp hy).1
        (congrArg Prod.fst he)) (congrArg (fun p : Bits × Bits => p.2) he)
    · intro y hy
      obtain ⟨hym, hyr⟩ := Finset.mem_product.mp hy
      obtain ⟨x, hx, he⟩ := h₁.surjOn hym
      exact ⟨(x, y.2), Finset.mem_product.mpr ⟨hx, hyr⟩, Prod.ext he rfl⟩
  exact h₂.comp h

open ConstructionContracts HybridContracts

set_option maxHeartbeats 500000 in
/-- The ideal sampler outputs independent repeated samples, uniform prefix
bits, and the full uniform affine key. The padding preserves entropy. -/
theorem idealGeneratorEntropy : IdealGeneratorEntropyContract := by
  intro F a k N j hFn hj n
  let t := k n * F.t n
  let L := k n * F.ℓ n
  let U := N n
  let d := j n
  let P := keyWidth U
  have hJ : d ≤ U := hj n
  let S := (cube t ×ˢ cube U) ×ˢ cube P
  let out : (Bits × Bits) × Bits → (Bits × Bits) × Bits :=
    fun q => ((repeatEval F k (a n) n q.1.1, q.1.2.take d), q.2)
  let format : (Bits × Bits) × Bits → Bits :=
    fun q => q.1.1 ++ (q.1.2 ++ List.replicate (U-d) false) ++ q.2
  let append : (Bits × Bits) × Bits → Bits := fun q => q.1.1 ++ q.1.2 ++ q.2
  let G := idealGenerator F k N
  let f := G.f (packAdvice a j n) n
  have hSeed : Set.BijOn append ↑S ↑(cube (G.t n)) := append_three_bijOn t U P
  have hAgree : Set.EqOn (f ∘ append) (format ∘ out) ↑S := by
    rintro ⟨⟨x, u⟩, r⟩ hmem
    obtain ⟨hxu, hr⟩ := Finset.mem_product.mp hmem
    obtain ⟨hx, hu⟩ := Finset.mem_product.mp hxu
    have hX := mem_cube_iff_length.mp hx
    have hU := mem_cube_iff_length.mp hu
    have hR := mem_cube_iff_length.mp hr
    have hXU : (x ++ u).length = t + U := by simp [hX, hU]
    change ((idealGenerator F k N).f (Nat.pair (a n) (j n)) n ((x ++ u) ++ r)) =
      repeatEval F k (a n) n x ++ (u.take d ++ List.replicate (U-d) false) ++ r
    simp only [idealGenerator, Nat.unpair_pair, min_eq_left (hj n)]
    have hTake : ((x ++ u) ++ r).take t = x := by
      rw [List.append_assoc, List.take_left' hX]
    have hDrop : ((x ++ u) ++ r).drop t = u ++ r := by
      rw [List.append_assoc, List.drop_left' hX]
    change repeatEval F k (a n) n (((x ++ u) ++ r).take t) ++
      padPrefix U d ((((x ++ u) ++ r).drop t).take U) ++
      ((((x ++ u) ++ r).drop (t + U)).take P) = _
    rw [hTake, hDrop, List.take_left' hU, List.drop_left' hXU, List.take_of_length_le hR.le]
    rfl
  have hOut (q : (Bits × Bits) × Bits) (hq : q ∈ S) :
      (out q).1.1.length = L ∧ (out q).1.2.length = d ∧ (out q).2.length = P := by
    obtain ⟨hxu, hr⟩ := Finset.mem_product.mp hq
    obtain ⟨hx, hu⟩ := Finset.mem_product.mp hxu
    exact ⟨repeatEval_length F a k n (hFn n) _ hx,
      by simp [out, mem_cube_iff_length.mp hu, min_eq_left hJ],
      mem_cube_iff_length.mp hr⟩
  have hPad (y : Bits) (hy : y.length = d) :
      (y ++ List.replicate (U-d) false).length = U := by
    simp only [List.length_append, List.length_replicate, hy]
    have h := hj n
    dsimp [U, d]
    omega
  have hEmbed : Set.InjOn format ↑(S.image out) := by
    intro y hy z hz he
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hL, hD, hP⟩ := hOut q hq
    obtain ⟨hL', hD', hP'⟩ := hOut r hr
    let u := (out q).1.2 ++ List.replicate (U-d) false
    let v := (out r).1.2 ++ List.replicate (U-d) false
    have hu : u.length = U := hPad _ hD
    have hv : v.length = U := hPad _ hD'
    have hCat : ((out q).1.1 ++ u).length = L + U := by simp [hL, hu]
    have hCat' : ((out r).1.1 ++ v).length = L + U := by simp [hL', hv]
    change (out q).1.1 ++ u ++ (out q).2 = (out r).1.1 ++ v ++ (out r).2 at he
    have hKey : (out q).2 = (out r).2 := by
      simpa only [List.drop_left' hCat, List.drop_left' hCat'] using
        (congrArg (List.drop (L + U)) he)
    have hPrefix : (out q).1.1 ++ u = (out r).1.1 ++ v :=
      List.append_cancel_right (show _ ++ (out r).2 = _ ++ (out r).2 by simpa only [hKey] using he)
    have hLeft : (out q).1.1 = (out r).1.1 := by
      simpa only [List.take_left' hL, List.take_left' hL'] using
        (congrArg (List.take L) (show (out q).1.1 ++ u = (out r).1.1 ++ v from hPrefix))
    have hMiddle : u = v := by
      simpa only [List.drop_left' hL, List.drop_left' hL'] using
        (congrArg (List.drop L) (show (out q).1.1 ++ u = (out r).1.1 ++ v from hPrefix))
    have hCenter : (out q).1.2 = (out r).1.2 := by
      simpa only [u, v, List.take_left' hD, List.take_left' hD'] using
        (congrArg (List.take d) hMiddle)
    exact Prod.ext (Prod.ext hLeft hCenter) hKey
  have hMap (x : Bits) (hx : x ∈ cube (G.t n)) : f x ∈ cube (G.ℓ n) := by
    obtain ⟨q, hq, rfl⟩ := hSeed.surjOn hx
    have hq' : f (append q) = format (out q) := hAgree hq
    obtain ⟨hL, hD, hP⟩ := hOut q hq
    apply mem_cube_iff_length.mpr
    rw [hq']
    change (format (out q)).length = L + U + P
    simp only [format, List.length_append, hL, hP, hPad _ hD]
  let H := (k n : ℝ) * shannonOn (cube (F.ℓ n)) (F.law a n)
  let f₁ := repeatEval F k (a n) n
  let f₂ : Bits → Bits := List.take d
  let pairOut : Bits × Bits → Bits × Bits := fun q => (f₁ q.1, f₂ q.2)
  have hFirst : entropyOf (cube t) f₁ = H := entropyOf_repeat F a k n (hFn n)
  have hSecond : entropyOf (cube U) f₂ = (d : ℝ) := entropyOf_cubePrefix hJ
  have hThird : entropyOf (cube P) id = (P : ℝ) := entropyOf_uniformCube P
  have hPair : entropyOf (cube t ×ˢ cube U) pairOut = H + (d : ℝ) :=
    (entropyOf_product (cube t) (cube U) (Proposed.cube_nonempty t)
      (Proposed.cube_nonempty U) f₁ f₂).trans (congrArg₂ (· + ·) hFirst hSecond)
  have hTriple : entropyOf S out = H + (d : ℝ) + (P : ℝ) :=
    (entropyOf_product (cube t ×ˢ cube U) (cube P)
      ((Proposed.cube_nonempty t).product (Proposed.cube_nonempty U))
      (Proposed.cube_nonempty P) pairOut id).trans (congrArg₂ (· + ·) hPair hThird)
  have h1 : entropyOf (cube (G.t n)) f = shannonOn (cube (G.ℓ n)) (lawOn (cube (G.t n)) f) :=
    Proposed.entropyOfOnSuperset (cube (G.t n)) (cube (G.ℓ n)) f hMap
  have h2 : entropyOf S (f ∘ append) = entropyOf (cube (G.t n)) f :=
    entropyOf_eq_of_bijOn hSeed f
  have h3 : entropyOf S (f ∘ append) = entropyOf S (format ∘ out) := entropyOf_congr S hAgree
  have h4 : entropyOf S (format ∘ out) = entropyOf S out :=
    entropyOf_injective_map S out format hEmbed
  change shannonOn (cube (G.ℓ n)) (lawOn (cube (G.t n)) f) = H + (d : ℝ) + (P : ℝ)
  exact h1.symm.trans (h2.symm.trans (h3.trans (h4.trans hTriple)))

end HILL.PRG

end HILL416_IdealEntropy

section HILL416_AffineRows

namespace HILL.PRG

private theorem parity_succ (n : ℕ) :
    ((n + 1) % 2 == 1) = !(n % 2 == 1) := by
  have h : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases h with h | h <;> simp [Nat.add_mod n 1 2, h]

theorem ip_cons (a b : Bool) (x y : Bits) :
    ip (a :: x) (b :: y) = Bool.xor (a && b) (ip x y) := by
  cases a <;> cases b <;> simp [ip, List.zip_cons_cons]
  exact parity_succ _

private theorem innerXor (a b c p q : Bool) :
    Bool.xor (Bool.xor (a && b) p) (Bool.xor (a && c) q) =
      Bool.xor (a && Bool.xor b c) (Bool.xor p q) := by
  cases a <;> cases b <;> cases c <;> cases p <;> cases q <;> rfl

theorem ip_xor_right (c x y : Bits) (h : x.length = y.length) :
    ip c (List.zipWith Bool.xor x y) = Bool.xor (ip c x) (ip c y) := by
  induction c generalizing x y with
  | nil => simp [ip]
  | cons a c ih =>
    cases x with
    | nil =>
      have hy : y = [] := List.length_eq_zero_iff.mp h.symm
      simp [hy, ip]
    | cons b x =>
      cases y with
      | nil => simp at h
      | cons d y =>
        have hl : x.length = y.length := by simpa using h
        simp only [List.zipWith_cons_cons, ip_cons, ih x y hl, innerXor]

theorem xor_zip_has_true (x y : Bits) (h : x.length = y.length) (hxy : x ≠ y) :
    true ∈ List.zipWith Bool.xor x y := by
  induction x generalizing y with
  | nil => exact False.elim (hxy (List.length_eq_zero_iff.mp h.symm).symm)
  | cons a x ih =>
    cases y with
    | nil => simp at h
    | cons b y =>
      by_cases hab : a = b
      · subst b
        have hLen : x.length = y.length := by simpa using h
        have hNe : x ≠ y := fun he => hxy (congrArg (List.cons a) he)
        exact List.mem_cons_of_mem _ (ih y hLen hNe)
      · have hxor : Bool.xor a b = true := by cases a <;> cases b <;> simp_all
        exact List.mem_cons.mpr (Or.inl hxor.symm)

private theorem xor_eq_false_iff (a b : Bool) : Bool.xor a b = false ↔ a = b := by
  cases a <;> cases b <;> decide

private theorem card_cube_filter_tail (N : ℕ) (p : Bits → Prop) [DecidablePred p] :
    ((cube (N + 1)).filter (fun x => p x.tail)).card =
      2 * ((cube N).filter p).card := by
  let S := (Finset.univ : Finset Bool) ×ˢ (cube N).filter p
  let T := (cube (N + 1)).filter (fun x => p x.tail)
  have h : Set.BijOn (fun q : Bool × Bits => q.1 :: q.2) ↑S ↑T := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨b, x⟩ hx
      obtain ⟨_, h⟩ := Finset.mem_product.mp hx
      obtain ⟨hLen, hP⟩ := Finset.mem_filter.mp h
      exact Finset.mem_filter.mpr ⟨mem_cube_iff_length.mpr (by simp [mem_cube_iff_length.mp hLen]), hP⟩
    · rintro ⟨b, x⟩ _ ⟨c, y⟩ _ he
      simpa only [List.cons.injEq, Prod.mk.injEq] using he
    · intro z hz
      obtain ⟨hl, hp⟩ := Finset.mem_filter.mp hz
      cases z with
      | nil => simp [mem_cube_iff_length] at hl
      | cons b w =>
        have hw : w.length = N := by simpa using mem_cube_iff_length.mp hl
        exact ⟨(b, w), Finset.mem_product.mpr
          ⟨Finset.mem_univ _, Finset.mem_filter.mpr ⟨mem_cube_iff_length.mpr hw, hp⟩⟩, rfl⟩
  rw [← finset_card_eq_of_bijOn h]
  simp [S]

private theorem card_even_innerProduct (w : Bits) (hw : true ∈ w) :
    ((cube w.length).filter (fun c => ip c w = false)).card * 2 = 2 ^ w.length := by
  induction w with
  | nil => simp at hw
  | cons b w ih =>
    cases b with
    | false =>
      have hFilter : (cube (false :: w).length).filter (fun c => ip c (false :: w) = false) =
          (cube (w.length + 1)).filter (fun c => ip c.tail w = false) := by
        ext c
        have hc : ip c (false :: w) = ip c.tail w := by cases c <;> simp [ip]
        simp only [List.length_cons, Finset.mem_filter, hc]
      rw [hFilter, card_cube_filter_tail w.length (fun c => ip c w = false)]
      have h := ih (by simpa using hw)
      rw [List.length_cons, pow_succ, Nat.mul_comm (2 ^ w.length) 2, ← h, Nat.mul_assoc]
    | true =>
      have h : Set.BijOn (fun c : Bits => c.tail)
          ↑((cube (w.length + 1)).filter (fun c => ip c (true :: w) = false)) ↑(cube w.length) := by
        refine ⟨?_, ?_, ?_⟩
        · intro c hc
          apply mem_cube_iff_length.mpr
          have hl := mem_cube_iff_length.mp (Finset.mem_filter.mp hc).1
          simp [hl]
        · intro c hc d hd he
          obtain ⟨hcL, hcI⟩ := Finset.mem_filter.mp hc
          obtain ⟨hdL, hdI⟩ := Finset.mem_filter.mp hd
          cases c with
          | nil => simp [mem_cube_iff_length] at hcL
          | cons a c =>
            cases d with
            | nil => simp [mem_cube_iff_length] at hdL
            | cons b d =>
              have ha : a = ip c w := by
                apply (xor_eq_false_iff _ _).mp
                simpa only [ip_cons, Bool.and_true] using hcI
              have hb : b = ip d w := by
                apply (xor_eq_false_iff _ _).mp
                simpa only [ip_cons, Bool.and_true] using hdI
              simp only [List.cons.injEq]
              exact ⟨ha.trans ((congrArg (fun v => ip v w) he).trans hb.symm), he⟩
        · intro c hc
          refine ⟨ip c w :: c, Finset.mem_filter.mpr ⟨mem_cube_iff_length.mpr ?_, ?_⟩, rfl⟩
          · simp [mem_cube_iff_length.mp hc]
          · simp [ip_cons]
      rw [List.length_cons, finset_card_eq_of_bijOn h, Proposed.cube_card, pow_succ]

private def rowOutput (r x : Bits) : Bool := Bool.xor (r.headD false) (ip r.tail x)

private theorem row_collision_card {N : ℕ} (x y : Bits)
    (hx : x.length = N) (hy : y.length = N) (hxy : x ≠ y) :
    ((cube (N + 1)).filter (fun r => rowOutput r x = rowOutput r y)).card = 2 ^ N := by
  let w := List.zipWith Bool.xor x y
  have hLen : w.length = N := by simp [w, hx, hy]
  have hTrue : true ∈ w := xor_zip_has_true x y (hx.trans hy.symm) hxy
  have hFilt : (cube (N + 1)).filter (fun r => rowOutput r x = rowOutput r y) =
      (cube (N + 1)).filter (fun r => ip r.tail w = false) := by
    ext r
    rw [Finset.mem_filter, Finset.mem_filter]
    simp only [rowOutput, w, ip_xor_right _ _ _ (hx.trans hy.symm)]
    apply and_congr_right
    intro _
    cases r.headD false <;> cases ip r.tail x <;> cases ip r.tail y <;> decide
  rw [hFilt, card_cube_filter_tail N (fun c => ip c w = false), Nat.mul_comm 2]
  simpa only [hLen] using card_even_innerProduct w hTrue

private theorem rowOutput_eq_key_bit (r x : Bits) {N : ℕ} (hx : x.length = N)
    (i : Fin N) :
    rowOutput (Blocks.block (N + 1) r i) x =
      Bool.xor (r.getD (i.val * (N + 1)) false)
        (ip ((r.drop (i.val * (N + 1) + 1)).take N) (x.take N)) := by
  rw [List.take_of_length_le hx.le]
  let d := i.val * (N + 1)
  have hHead : (r.drop d).headD false = r.getD d false := by
    simp [List.getD_eq_getElem?_getD]
  have hTail : r.drop (d + 1) = (r.drop d).tail := by
    rw [← List.drop_drop]
    simp
  change rowOutput ((r.drop d).take (N + 1)) x =
    Bool.xor (r.getD d false) (ip ((r.drop (d + 1)).take N) x)
  unfold rowOutput
  rw [← hHead, hTail]
  cases r.drop d <;> simp

open scoped BigOperators
open ConstructionContracts

set_option maxHeartbeats 1000000 in
/-- For distinct inputs each retained affine row imposes one independent
bit constraint on the full key. -/
theorem affineCollision : AffineCollisionContract := by
  intro N j hj x hx y hy hxy
  classical
  have hX := mem_cube_iff_length.mp hx
  have hY := mem_cube_iff_length.mp hy
  let R := cube (N + 1)
  let A := R.filter (fun r => rowOutput r x = rowOutput r y)
  let Q := Fintype.piFinset (fun _ : Fin N => R)
  let U : Fin N → Finset Bits := fun i => if i.val < j then A else R
  let S := Fintype.piFinset U
  let D := (cube (keyWidth N)).filter (fun r => affinePrefix N j r x = affinePrefix N j r y)
  have hQ := Blocks.flatten_bijOn N (N + 1)
  have hKey (rs : Fin N → Bits) (hrs : rs ∈ Q) :
      Blocks.flatten rs ∈ D ↔ rs ∈ S := by
    have hLen (i : Fin N) : (rs i).length = N + 1 :=
      mem_cube_iff_length.mp (Fintype.mem_piFinset.mp hrs i)
    have hEq :
        affinePrefix N j (Blocks.flatten rs) x = affinePrefix N j (Blocks.flatten rs) y ↔
          ∀ i : Fin N, i.val < j → rowOutput (rs i) x = rowOutput (rs i) y := by
      simp only [affinePrefix, List.map_inj_left, List.mem_range]
      constructor
      · intro h i hi
        rw [← Blocks.block_flatten rs hLen i, rowOutput_eq_key_bit _ _ hX, rowOutput_eq_key_bit _ _ hY]
        exact h i.val hi
      · intro h i hi
        let k : Fin N := ⟨i, hi.trans_le hj⟩
        have he := h k hi
        rw [← Blocks.block_flatten rs hLen k, rowOutput_eq_key_bit _ _ hX,
          rowOutput_eq_key_bit _ _ hY] at he
        exact he
    change
      Blocks.flatten rs ∈ (cube (keyWidth N)).filter
        (fun r => affinePrefix N j r x = affinePrefix N j r y) ↔
      rs ∈ Fintype.piFinset U
    rw [Finset.mem_filter, Fintype.mem_piFinset, hEq]
    have hMem : Blocks.flatten rs ∈ cube (keyWidth N) := hQ.mapsTo hrs
    constructor
    · rintro ⟨_, hh⟩ i
      have hRi : rs i ∈ R := Fintype.mem_piFinset.mp hrs i
      by_cases hi : i.val < j
      · simpa only [U, if_pos hi, A, Finset.mem_filter] using And.intro hRi (hh i hi)
      · simpa only [U, if_neg hi] using hRi
    · intro h
      refine ⟨hMem, fun i hi => ?_⟩
      simpa only [U, if_pos hi, A, Finset.mem_filter, and_iff_right
        (Fintype.mem_piFinset.mp hrs i)] using h i
  have hSubset : S ⊆ Q := by
    intro rs hrs
    apply Fintype.mem_piFinset.mpr
    intro i
    have hi := Fintype.mem_piFinset.mp hrs i
    by_cases h : i.val < j
    · exact (Finset.mem_filter.mp (by simpa only [U, if_pos h] using hi : rs i ∈ A)).1
    · simpa only [U, if_neg h] using hi
  have hBij : Set.BijOn (Blocks.flatten (k := N)) ↑S ↑D := by
    refine ⟨fun rs hr => (hKey rs (hSubset hr)).mpr hr, hQ.injOn.mono hSubset, ?_⟩
    intro r hr
    obtain ⟨rs, hrs, rfl⟩ := hQ.surjOn (Finset.mem_filter.mp hr).1
    exact ⟨rs, (hKey rs hrs).mp hr, rfl⟩
  have hSorted : ((Finset.univ : Finset (Fin N)).filter (fun i => i.val < j)).card = j := by
    refine (Finset.card_bij (t := Finset.range j) (fun i _ => i.val) ?_ ?_ ?_).trans
      (Finset.card_range j)
    · exact fun i hi => Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
    · exact fun i _ k _ he => Fin.ext he
    · intro i hi
      have hij := Finset.mem_range.mp hi
      exact ⟨⟨i, hij.trans_le hj⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩, rfl⟩
  have hTwo : (∏ i : Fin N, if i.val < j then (2 : ℕ) else 1) = 2 ^ j := by
    rw [Finset.prod_ite]
    simp [hSorted]
  have hA : A.card = 2 ^ N := row_collision_card x y hX hY hxy
  have hRow (i : Fin N) :
      (U i).card * (if i.val < j then (2 : ℕ) else 1) = 2 ^ (N + 1) := by
    by_cases h : i.val < j
    · simp [U, h, hA, pow_succ]
    · simp [U, h, R, Proposed.cube_card]
  change D.card * 2 ^ j = 2 ^ keyWidth N
  rw [← finset_card_eq_of_bijOn hBij, Fintype.card_piFinset, ← hTwo, ← Finset.prod_mul_distrib]
  simp only [hRow, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← pow_mul, keyWidth, Nat.mul_comm (N + 1) N]

theorem affinePrefix_length (N j : ℕ) (r x : Bits) :
    (affinePrefix N j r x).length = j := by
  simp [affinePrefix]

/-- Repeated-fiber extraction instantiated with the concrete affine hash. -/
theorem repeatedAffineExtraction (T k j m : ℕ) (f : Bits → Bits) (s : ℝ)
    (hk : 0 < k) (hs : 0 < s) (hJ : j ≤ k * T)
    (hWidth : j = Nat.floor ((k : ℝ) * ((T : ℝ) - entropyOf (cube T) f - s / 2)))
    (hm : 2 * (m : ℝ) ≤ (k : ℝ) * s / 4) :
    let N := k * T
    let S := Fintype.piFinset (fun _ : Fin k => cube T)
    let R := cube (keyWidth N)
    let Z := cube j
    let h : Bits → (Fin k → Bits) → Bits := fun r x => affinePrefix N j r (Blocks.flatten x)
    statDistOn (Proposed.hashSupportOn S R Z (Proposed.repeatEval f))
      (Proposed.hashActualOn S R (Proposed.repeatEval f) h)
      (Proposed.hashIdealOn S R Z (Proposed.repeatEval f)) ≤
      Real.exp (-((k : ℝ) * s ^ 2) / (8 * ((T : ℝ) + 1) ^ 2)) + 1 / (2 : ℝ) ^ (m + 1) := by
  dsimp only
  refine Proposed.repeatedUniformExtraction T k j m f (cube (keyWidth (k * T))) _
    s hk (Proposed.cube_nonempty _) hs hWidth hm ?_ ?_
  · intro r _ xs _
    exact mem_cube_iff_length.mpr (affinePrefix_length _ _ _ _)
  · intro x hx y hy hxy
    have hB := Blocks.flatten_bijOn k T
    have hCol := affineCollision (k * T) j hJ (Blocks.flatten x) (hB.mapsTo hx)
      (Blocks.flatten y) (hB.mapsTo hy) (fun he => hxy (hB.injOn hx hy he))
    rw [Proposed.cube_card, Proposed.cube_card, Nat.cast_pow, Nat.cast_ofNat, ← mul_comm]
    exact le_of_eq (by exact_mod_cast hCol)

end HILL.PRG

end HILL416_AffineRows

section HILL416_EncodedDistance

namespace HILL.PRG

open scoped BigOperators

theorem lawOn_congr {A B : Type*} [DecidableEq B]
    (S : Finset A) {f g : A → B} (h : Set.EqOn f g ↑S) :
    lawOn S f = lawOn S g := by
  funext b
  unfold lawOn
  have hFilter : S.filter (fun x => f x = b) = S.filter (fun x => g x = b) :=
    Finset.ext (fun x => by
      simp only [Finset.mem_filter]
      exact and_congr_right (fun hx => by rw [h hx]))
  rw [hFilter]

theorem lawOn_ignore_right {A B C : Type*} [DecidableEq C]
    (S : Finset A) (T : Finset B) (hT : T.Nonempty) (f : A → C) :
    lawOn (S ×ˢ T) (f ∘ Prod.fst) = lawOn S f := by
  funext y
  unfold lawOn
  have hFilter : (S ×ˢ T).filter (fun p => (f ∘ Prod.fst) p = y) =
      S.filter (fun x => f x = y) ×ˢ T := by
    ext ⟨x, z⟩
    simp only [Function.comp_apply, Finset.mem_filter, Finset.mem_product]
    tauto
  rw [hFilter]
  simp only [Finset.card_product, Nat.cast_mul,
    mul_div_mul_right _ _ (Nat.cast_ne_zero.mpr hT.card_ne_zero : (T.card : ℝ) ≠ 0)]

private theorem lawOn_encode_at {A B C : Type*} [DecidableEq B] [DecidableEq C]
    (S : Finset A) (V : Finset B) (f : A → B) (e : B → C)
    (hf : ∀ x ∈ S, f x ∈ V) (he : Set.InjOn e ↑V)
    (y : B) (hy : y ∈ V) :
    lawOn S (e ∘ f) (e y) = lawOn S f y := by
  unfold lawOn
  have hFilter : S.filter (fun x => (e ∘ f) x = e y) = S.filter (fun x => f x = y) :=
    Finset.ext (fun x => by
      simp only [Finset.mem_filter, Function.comp_apply]
      exact and_congr_right (fun hx => he.eq_iff (hf x hx) hy))
  rw [hFilter]

private theorem lawOn_encode_outside {A B C : Type*} [DecidableEq B] [DecidableEq C]
    (S : Finset A) (V : Finset B) (f : A → B) (e : B → C)
    (hf : ∀ x ∈ S, f x ∈ V) (y : C) (hy : y ∉ V.image e) :
    lawOn S (e ∘ f) y = 0 := by
  unfold lawOn
  have hFilter : S.filter (fun x => (e ∘ f) x = y) = ∅ :=
    Finset.filter_eq_empty_iff.mpr (fun x hx he => hy (Finset.mem_image.mpr ⟨f x, hf x hx, he⟩))
  rw [hFilter]
  simp

/-- Relabeling both finite distributions by an injective encoding preserves distance. -/
theorem statDistOn_encode {A B C D : Type*} [DecidableEq C] [DecidableEq D]
    (S : Finset A) (T : Finset B) (V : Finset C) (W : Finset D)
    (f : A → C) (g : B → C) (e : C → D)
    (hf : ∀ x ∈ S, f x ∈ V) (hg : ∀ x ∈ T, g x ∈ V)
    (he : Set.InjOn e ↑V) (hW : ∀ x ∈ V, e x ∈ W) :
    statDistOn W (lawOn S (e ∘ f)) (lawOn T (e ∘ g)) =
      statDistOn V (lawOn S f) (lawOn T g) := by
  unfold statDistOn
  have hSubset : V.image e ⊆ W := Finset.image_subset_iff.mpr hW
  have hZero (y : D) (_ : y ∈ W) (hy : y ∉ V.image e) :
      |lawOn S (e ∘ f) y - lawOn T (e ∘ g) y| = 0 := by
    rw [lawOn_encode_outside S V f e hf y hy, lawOn_encode_outside T V g e hg y hy,
      sub_zero, abs_zero]
  rw [← Finset.sum_subset hSubset hZero, Finset.sum_image he]
  congr 1
  exact Finset.sum_congr rfl (fun y hy => by
    rw [lawOn_encode_at S V f e hf he y hy, lawOn_encode_at T V g e hg he y hy])

end HILL.PRG

end HILL416_EncodedDistance

section HILL416_ConstructionExtraction

namespace HILL.PRG

open ConstructionContracts HybridContracts

set_option maxHeartbeats 1000000 in
/-- Transport the affine extraction estimate to the generator's fixed-width bit strings. -/
theorem constructionExtraction : ConstructionExtractionContract := by
  intro F a k j s n _hn hLen hs hWidth hmargin hvar
  let T := F.t n
  let K := k n
  let J := j n
  let N := K * T
  let P := keyWidth N
  let L := K * F.ℓ n
  let X := Fin K → Bits
  let S : Finset X := Fintype.piFinset (fun _ => cube T)
  let R := cube P
  let Z := cube J
  let Extra := cube (N - J)
  let A := S ×ˢ R
  let I := A ×ˢ Z
  let IExt := I ×ˢ Extra
  let f := F.f (a n) n
  let rep : X → X := Proposed.repeatEval f
  let h : Bits → X → Bits := fun r x => affinePrefix N J r (Blocks.flatten x)
  let V := Proposed.hashSupportOn S R Z rep
  let rawA : X × Bits → X × (Bits × Bits) := fun q => (rep q.1, (q.2, h q.2 q.1))
  let rawI : (X × Bits) × Bits → X × (Bits × Bits) :=
    fun q => (rep q.1.1, (q.1.2, q.2))
  let b := packAdvice a j
  let G := hashGenerator F k
  let W := idealGenerator F k (seedWidth F k)
  have hJ : J ≤ N := by
    change j n ≤ k n * F.t n
    rw [hWidth]
    exact hashWidthBound (F.t n) (k n) _ _ (shannonOn_lawOn_nonneg _ _ _) hs.le
  have hK : 0 < K := by
    by_contra hK
    have hz : k n = 0 := Nat.eq_zero_of_not_pos hK
    rw [hz, Nat.cast_zero, zero_mul] at hmargin
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hN : J + (N - J) = N := by omega
  let pack : X × (Bits × Bits) → (Bits × Bits) × Bits :=
    fun q => ((Blocks.flatten q.1, q.2.2 ++ List.replicate (N-J) false), q.2.1)
  let enc : X × (Bits × Bits) → Bits := fun q =>
    (pack q).1.1 ++ (pack q).1.2 ++ (pack q).2
  have hPack : Set.MapsTo pack ↑V ↑((cube L ×ˢ cube N) ×ˢ cube P) := by
    intro q hq
    have hv : q ∈ (S.image rep) ×ˢ (R ×ˢ Z) := hq
    obtain ⟨hF, hRZ⟩ := Finset.mem_product.mp hv
    obtain ⟨hr, hz⟩ := Finset.mem_product.mp hRZ
    obtain ⟨xs, hxs, he⟩ := Finset.mem_image.mp hF
    have hB (i : Fin K) : (q.1 i).length = F.ℓ n := by
      rw [← he]
      exact hLen (xs i) (Fintype.mem_piFinset.mp hxs i)
    refine Finset.mem_product.mpr ⟨Finset.mem_product.mpr
      ⟨mem_cube_iff_length.mpr (Blocks.flatten_length q.1 hB), ?_⟩, hr⟩
    apply mem_cube_iff_length.mpr
    change (q.2.2 ++ List.replicate (N-J) false).length = N
    simp only [List.length_append, List.length_replicate, mem_cube_iff_length.mp hz, hN]
  have hEnc : Set.InjOn enc ↑V := by
    intro q hq u hu he
    have hP : pack q = pack u :=
      (append_three_bijOn L N P).injOn (hPack hq) (hPack hu) he
    have hQ : q ∈ (S.image rep) ×ˢ (R ×ˢ Z) := hq
    have hU : u ∈ (S.image rep) ×ˢ (R ×ˢ Z) := hu
    have outputBlocks (q : X × (Bits × Bits)) (hq : q ∈ (S.image rep) ×ˢ (R ×ˢ Z)) :
        q.1 ∈ Fintype.piFinset (fun _ : Fin K => cube (F.ℓ n)) := by
      obtain ⟨xs, hx, he⟩ := Finset.mem_image.mp (Finset.mem_product.mp hq).1
      rw [← he]
      exact Fintype.mem_piFinset.mpr fun i =>
        mem_cube_iff_length.mpr (hLen _ (Fintype.mem_piFinset.mp hx i))
    have hx : q.1 = u.1 := (Blocks.flatten_bijOn K (F.ℓ n)).injOn
      (outputBlocks q hQ) (outputBlocks u hU)
      (congrArg (fun p : (Bits × Bits) × Bits => p.1.1) hP)
    have hz : q.2.2 = u.2.2 := by
      have h := congrArg (fun p : (Bits × Bits) × Bits => p.1.2) hP
      change q.2.2 ++ List.replicate (N-J) false = u.2.2 ++ List.replicate (N-J) false at h
      exact List.append_cancel_right h
    exact Prod.ext hx (Prod.ext (congrArg (fun p : (Bits × Bits) × Bits => p.2) hP) hz)
  have hWMap : ∀ z ∈ V, enc z ∈ cube (G.ℓ n) :=
    fun q hq => (append_three_bijOn L N P).mapsTo (hPack hq)
  have hRawA : ∀ q ∈ A, rawA q ∈ V := by
    intro q hq
    obtain ⟨hx, hr⟩ := Finset.mem_product.mp hq
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem rep hx, Finset.mem_product.mpr
      ⟨hr, mem_cube_iff_length.mpr (affinePrefix_length _ _ _ _)⟩⟩
  have hRawI : ∀ q ∈ I, rawI q ∈ V := by
    intro q hq
    obtain ⟨hA, hz⟩ := Finset.mem_product.mp hq
    obtain ⟨hx, hr⟩ := Finset.mem_product.mp hA
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem rep hx, Finset.mem_product.mpr ⟨hr, hz⟩⟩
  let seedA : X × Bits → Bits := fun q => Blocks.flatten q.1 ++ q.2
  have hA1 : Set.BijOn (fun q : X × Bits => (Blocks.flatten q.1, q.2))
      ↑A ↑(cube N ×ˢ R) := by
    simpa only [A, S, N, X, Finset.coe_product, id_eq] using (Blocks.flatten_bijOn K T).prodMap
      (Set.bijOn_id (s := (↑R : Set Bits)))
  have hSeedA : Set.BijOn seedA ↑A ↑(cube (G.t n)) := (append_bijOn N P).comp hA1
  let seedI : ((X × Bits) × Bits) × Bits → Bits := fun q =>
    Blocks.flatten q.1.1.1 ++ (q.1.2 ++ q.2) ++ q.1.1.2
  have hI1 : Set.BijOn
      (fun q : ((X × Bits) × Bits) × Bits => ((q.1.1.1, (q.1.2, q.2)), q.1.1.2))
      ↑IExt ↑((S ×ˢ (Z ×ˢ Extra)) ×ˢ R) := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨⟨⟨x, r⟩, z⟩, u⟩ hq
      simpa only [IExt, I, A, Finset.mem_coe, Finset.mem_product, and_assoc, and_left_comm,
        and_comm] using hq
    · rintro ⟨⟨⟨x, r⟩, z⟩, u⟩ _ ⟨⟨⟨x', r'⟩, z'⟩, u'⟩ _ he
      simp only [Prod.mk.injEq] at he ⊢
      tauto
    · rintro ⟨⟨x, ⟨z, u⟩⟩, r⟩ hq
      refine ⟨⟨⟨⟨x, r⟩, z⟩, u⟩, ?_, rfl⟩
      simpa only [IExt, I, A, Finset.mem_coe, Finset.mem_product, and_assoc, and_left_comm,
        and_comm] using hq
  have hAppend : Set.BijOn (fun q : Bits × Bits => q.1 ++ q.2) ↑(Z ×ˢ Extra) ↑(cube N) := by
    simpa only [hN] using append_bijOn J (N-J)
  have hI2 : Set.BijOn (fun q : (X × (Bits × Bits)) × Bits =>
      ((Blocks.flatten q.1.1, q.1.2.1 ++ q.1.2.2), q.2))
      ↑((S ×ˢ (Z ×ˢ Extra)) ×ˢ R) ↑((cube N ×ˢ cube N) ×ˢ R) := by
    simpa only [S, N, X, Finset.coe_product, id_eq] using ((Blocks.flatten_bijOn K T).prodMap hAppend).prodMap
      (Set.bijOn_id (s := (↑R : Set Bits)))
  have hSeedI : Set.BijOn seedI ↑IExt ↑(cube (W.t n)) :=
    (append_three_bijOn N N P).comp (hI2.comp hI1)
  let fa := G.f (b n) n
  let fi := W.f (b n) n
  have repeatEq (xs : X) (hx : xs ∈ S) :
      repeatEval F k (a n) n (Blocks.flatten xs) = Blocks.flatten (rep xs) :=
    repeatEval_flatten F a k n xs (fun i => mem_cube_iff_length.mp (Fintype.mem_piFinset.mp hx i))
  have hAgreeA : Set.EqOn (fa ∘ seedA) (enc ∘ rawA) ↑A := by
    rintro ⟨x, r⟩ hq
    obtain ⟨hx, hr⟩ := Finset.mem_product.mp hq
    have hxN := mem_cube_iff_length.mp ((Blocks.flatten_bijOn K T).mapsTo hx)
    have hrP := mem_cube_iff_length.mp hr
    change (hashGenerator F k).f (Nat.pair (a n) (j n)) n (Blocks.flatten x ++ r) = _
    simp only [hashGenerator, Nat.unpair_pair]
    change repeatEval F k (a n) n ((Blocks.flatten x ++ r).take N) ++
      paddedAffine N J (((Blocks.flatten x ++ r).drop N).take P)
        ((Blocks.flatten x ++ r).take N) ++ (((Blocks.flatten x ++ r).drop N).take P) = _
    rw [List.take_left' hxN, List.drop_left' hxN, List.take_of_length_le hrP.le, repeatEq x hx]
    simp only [paddedAffine, min_eq_left hJ]
    rfl
  have hAgreeI : Set.EqOn (fi ∘ seedI) ((enc ∘ rawI) ∘ Prod.fst) ↑IExt := by
    rintro ⟨⟨⟨x, r⟩, z⟩, u⟩ hq
    obtain ⟨hqi, hu⟩ := Finset.mem_product.mp hq
    obtain ⟨hqa, hz⟩ := Finset.mem_product.mp hqi
    obtain ⟨hx, hr⟩ := Finset.mem_product.mp hqa
    have hxN := mem_cube_iff_length.mp ((Blocks.flatten_bijOn K T).mapsTo hx)
    have hrP := mem_cube_iff_length.mp hr
    have hzJ := mem_cube_iff_length.mp hz
    have hzuN : (z ++ u).length = N := by
      rw [List.length_append, hzJ, mem_cube_iff_length.mp hu, hN]
    have hPrefix : (Blocks.flatten x ++ (z ++ u)).length = N + N := by simp [hxN, hzuN, N]
    let seed := Blocks.flatten x ++ (z ++ u) ++ r
    have hTake : seed.take N = Blocks.flatten x := by
      dsimp [seed]
      rw [List.append_assoc, List.take_left' hxN]
    have hDrop : seed.drop N = (z ++ u) ++ r := by
      dsimp [seed]
      rw [List.append_assoc, List.drop_left' hxN]
    change (idealGenerator F k (seedWidth F k)).f (Nat.pair (a n) (j n)) n seed = _
    have hMin : min (j n) (seedWidth F k n) = J := min_eq_left hJ
    simp only [idealGenerator, Nat.unpair_pair, hMin]
    change repeatEval F k (a n) n (seed.take N) ++
      padPrefix N J ((seed.drop N).take N) ++ ((seed.drop (N+N)).take P) = _
    rw [hTake, hDrop, List.take_left' hzuN, show seed.drop (N+N) = r from List.drop_left' hPrefix,
      List.take_of_length_le hrP.le, repeatEq x hx]
    simp only [padPrefix, List.take_left' hzJ]
    rfl
  have hGA : lawOn A (enc ∘ rawA) = G.law b n :=
    (lawOn_congr A hAgreeA.symm).trans (lawOn_eq_of_bijOn hSeedA fa)
  have hWI : lawOn I (enc ∘ rawI) = W.law b n :=
    (lawOn_ignore_right I Extra (Proposed.cube_nonempty _) (enc ∘ rawI)).symm.trans
      ((lawOn_congr IExt hAgreeI.symm).trans (lawOn_eq_of_bijOn hSeedI fi))
  have hEstimate := repeatedAffineExtraction T K J (n+1) f (s n) hK hs hJ
    (by rw [Proposed.entropyOfOnSuperset _ (cube (F.ℓ n)) _ (fun x hx =>
        mem_cube_iff_length.mpr (hLen x hx))]
        exact hWidth)
    (by push_cast; linarith)
  change statDistOn (cube (G.ℓ n)) (G.law b n) (W.law b n) ≤ extractionError n
  rw [← hGA, ← hWI, statDistOn_encode A I V (cube (G.ℓ n)) rawA rawI enc hRawA hRawI hEnc hWMap]
  have hExp : Real.exp (-((K : ℝ) * (s n) ^ 2) / (8 * ((T : ℝ) + 1) ^ 2)) ≤
      Real.exp (-((n : ℝ) + 1)) := by
    exact Real.exp_le_exp.mpr (by rw [neg_div]; exact neg_le_neg hvar)
  exact hEstimate.trans (add_le_add_left hExp _)

end HILL.PRG

end HILL416_ConstructionExtraction

section HILL416_MachineLemmas

/-!
# HILL 4.16: checked machine and random-tape lemmas

This file contains actual proofs, not unproved contract declarations.

Primary result:
  HILL.PRG.UnpairMachine.decodeWord_polytime
computes the two terminated unary fields of Nat.unpair of the input length.
The input bits may be arbitrary. The explicit fixed TM2 machine has seven
Boolean stacks, nine labels, and Option Bool control. Its time polynomial is
(X + 1) * (20 * X + 32). Every work stack is empty at termination.

Additional results:
* HILL.PRG.RowParityMachine.evaluate_polytime: an explicit affine-row parity
  machine, with time polynomial X + 1.
* HILL.PRG.HybridTape.uniformProb_three_slices: exact independence of three
  disjoint random-tape blocks, unaffected by unused suffix padding.
* HILL.PRG.HybridTape.acceptProb_eq_three_of_run: the corresponding exact
  acceptance identity from an explicit simulator run equation.

Validation environment: Lean v4.33.1 and Mathlib
0df444a360eaa60ab8c11dca51a86af692955474. The original HILL and Levin model
declaration bodies are unchanged in the checking harness; only broad imports
in those dependencies are replaced by focused imports from the same revision.
The combined file compiled successfully with no errors or warnings. Axiom
audits of both machine certificates, row correctness, paired-length decoding,
and both main probability lemmas report only propext, Classical.choice, and
Quot.sound, with no sorryAx. This file retains the canonical model import.
The complete user project and the original full-import Prove2Me environment
have not been rebuilt.

This does not prove the whole HILL 4.16 theorem, the full affine evaluator,
or the uniform hybrid wrapper's polynomial-time certificate. The acceptance
lemma keeps the wrapper's pointwise run equation as an explicit premise.

The code reuses the TM2 phase-proof style of the supplied BlockFormatter and
the supplied square-walk arithmetic, without requiring the unavailable
project helper modules. No extra axiom, sorry, or unsafe proof shortcut is used.
-/

/-! ## Source component: HILL416_UnpairArithmetic.lean -/

/-! Arithmetic invariants and polynomial budgets for a unary pairing decoder. -/

namespace HILL.PRG.UnpairArithmetic

theorem decode_eq_unpair {t r m : ℕ}
    (hEq : t * t + r = m) (hLe : r ≤ 2 * t) :
    (if r < t then (r, t) else (t, r - t)) = Nat.unpair m := by
  let decoded : ℕ × ℕ := if r < t then (r, t) else (t, r - t)
  have hCode : Nat.pair decoded.1 decoded.2 = m := by
    dsimp [decoded]
    split_ifs with hR
    · simpa only [Nat.pair, Prod.fst, Prod.snd, if_pos hR] using hEq
    · have hSub : ¬ t < r - t := by omega
      simp only [Nat.pair, if_neg hSub]
      omega
  change decoded = Nat.unpair m
  calc
    decoded = Nat.unpair (Nat.pair decoded.1 decoded.2) := by simp
    _ = Nat.unpair m := congrArg Nat.unpair hCode

theorem decoded_sum_le {t r m : ℕ}
    (hEq : t * t + r = m) (hLe : r ≤ 2 * t) :
    let decoded := if r < t then (r, t) else (t, r - t)
    decoded.1 + decoded.2 ≤ m := by
  dsimp only
  rw [decode_eq_unpair hEq hLe]
  exact Nat.unpair_add_le m

theorem state_bounds {t r g m : ℕ}
    (hEq : t * t + r = m) (hGap : r + g = 2 * t) :
    t ≤ m ∧ r ≤ 2 * m ∧ g ≤ 2 * m := by
  have ht : t ≤ t * t := by
    cases t with
    | zero => simp
    | succ t => nlinarith
  constructor
  · omega
  constructor <;> omega

theorem token_step_invariant {t r g m : ℕ}
    (hEq : t * t + r = m) (hGap : r + (g + 1) = 2 * t) :
    t * t + (r + 1) = m + 1 ∧ (r + 1) + g = 2 * t := by
  constructor <;> omega

theorem rollover_invariant {t r m : ℕ}
    (hEq : t * t + r = m) (hR : r = 2 * t) :
    (t + 1) * (t + 1) + 0 = m + 1 ∧ 0 + (r + 2) = 2 * (t + 1) := by
  constructor
  · nlinarith
  · omega

theorem reset_cost_le {t r g m : ℕ}
    (hEq : t * t + r = m) (hGap : r + g = 2 * t) :
    r + 4 ≤ 2 * (m + 1) + 2 := by
  have hr := (state_bounds hEq hGap).2.1
  omega

/-- The budget for n remaining ticks when q tokens have already been processed.
The constant c controls a per-tick allowance of 2*q+c+1. -/
def walkBudget (c q n : ℕ) : ℕ := n * (2 * q + n + c)

theorem walkBudget_zero (c q : ℕ) : walkBudget c q 0 = 0 := by
  simp [walkBudget]

theorem walkBudget_succ (c q n : ℕ) :
    walkBudget c q (n + 1) = 2 * q + c + 1 + walkBudget c (q + 1) n := by
  simp only [walkBudget]
  ring

theorem walkBudget_three_succ (q n : ℕ) :
    walkBudget 3 q (n + 1) = (2 * (q + 1) + 2) + walkBudget 3 (q + 1) n := by
  simp only [walkBudget]
  ring

theorem walkBudget_le_square (c q n : ℕ) :
    walkBudget c q n ≤ (q + n + c) ^ 2 := by
  unfold walkBudget
  nlinarith

theorem walkBudget_from_zero (c n : ℕ) :
    walkBudget c 0 n = n * (n + c) := by
  simp [walkBudget]

end HILL.PRG.UnpairArithmetic


/-! ## Source component: HILL416_UnpairMachine.lean -/

/-!
# A concrete unary decoder for Mathlib's natural pairing

The input bits are ignored; their number is decoded.  The result consists of
two terminated unary fields.  All work counters are stacks of Boolean tokens,
and the machine has a fixed finite set of labels and control states.
-/

set_option backward.isDefEq.respectTransparency.types false

namespace HILL.PRG.UnpairMachine

open Turing StateTransition UnpairArithmetic

noncomputable section

inductive Tape
  | input | root | remainder | gap | first | second | output
  deriving DecidableEq, Fintype

inductive Label
  | walk | reset | clearGap | compare | clearSecond | moveRemainder | moveRoot
  | emitSecond | emitFirst
  deriving DecidableEq, Fintype

private abbrev Γ : Tape → Type := fun _ => Bool
private abbrev Stmt := TM2.Stmt Γ Label (Option Bool)
private abbrev Cfg := TM2.Cfg Γ Label (Option Bool)

private def jump (l : Label) : Stmt :=
  .load (fun _ => none) (.goto (fun _ => l))

private def push (t : Tape) (b : Bool) (next : Stmt) : Stmt :=
  .push t (fun _ => b) next

private def token (t : Tape) (next : Stmt) : Stmt := push t true next

/-- Pop one token, remembering only whether the stack was empty. -/
private def has (t : Tape) (empty item : Stmt) : Stmt :=
  .pop t (fun _ b => b) (.branch Option.isSome item empty)

private def program : Label → Stmt
  | .walk =>
    has .input (jump .clearGap)
      (has .gap (token .root (jump .reset))
        (token .remainder (jump .walk)))
  | .reset =>
    has .remainder (token .gap (token .gap (jump .walk)))
      (token .gap (jump .reset))
  | .clearGap => has .gap (jump .compare) (jump .clearGap)
  | .compare =>
    has .root (jump .clearSecond)
      (has .remainder (token .root (jump .moveRoot))
        (token .first (token .second (jump .compare))))
  | .clearSecond => has .second (jump .moveRemainder) (jump .clearSecond)
  | .moveRemainder =>
    has .remainder (push .output false (jump .emitSecond))
      (token .second (jump .moveRemainder))
  | .moveRoot =>
    has .root (push .output false (jump .emitSecond))
      (token .second (jump .moveRoot))
  | .emitSecond =>
    has .second (push .output false (jump .emitFirst))
      (token .output (jump .emitSecond))
  | .emitFirst =>
    has .first (.load (fun _ => none) .halt)
      (token .output (jump .emitFirst))

private abbrev step := TM2.step program

private def unary (n : ℕ) : Bits := List.replicate n true

private def stk (xs : Bits) (t r g a b : ℕ) (out : Bits) : Tape → Bits
  | .input => xs
  | .root => unary t
  | .remainder => unary r
  | .gap => unary g
  | .first => unary a
  | .second => unary b
  | .output => out

private def cfg (l : Label) (xs : Bits) (t r g a b : ℕ) (out : Bits) : Cfg :=
  ⟨some l, none, stk xs t r g a b out⟩

private def done (out : Bits) : Cfg := ⟨none, none, stk [] 0 0 0 0 0 out⟩

private def machine : FinTM2 where
  K := Tape
  k₀ := .input
  k₁ := .output
  Γ := Γ
  Λ := Label
  main := .walk
  σ := Option Bool
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := program

private abbrev Run (x y : Cfg) (n : ℕ) := EvalsToInTime step x (some y) n

private def one {x y : Cfg} (h : step x = some y) : Run x y 1 :=
  ⟨⟨1, h⟩, le_rfl⟩

private def seq {a b c : Cfg} {m n : ℕ}
    (x : Run a b m) (y : Run b c n) : Run a c (m + n) :=
  ⟨(EvalsToInTime.trans _ _ _ _ _ _ x y).toEvalsTo,
    (Nat.add_le_add y.steps_le_m x.steps_le_m).trans_eq (Nat.add_comm _ _)⟩

private def relax {a b : Cfg} {m n : ℕ} (h : Run a b m) (hle : m ≤ n) : Run a b n :=
  ⟨h.toEvalsTo, h.steps_le_m.trans hle⟩

private theorem walk_token (bit : Bool) (xs : Bits) (t r g : ℕ) :
    step (cfg .walk (bit :: xs) t r (g + 1) 0 0 []) =
      some (cfg .walk xs t (r + 1) g 0 0 []) := by
  (simp [cfg, done, program, has, token, push, jump, stk, unary,
    List.replicate_succ, Function.update] <;>
    (funext k; cases k <;> simp [stk, unary, List.replicate_succ, Function.update]))

private theorem walk_rollover (bit : Bool) (xs : Bits) (t r : ℕ) :
    step (cfg .walk (bit :: xs) t r 0 0 0 []) =
      some (cfg .reset xs (t + 1) r 0 0 0 []) := by
  (simp [cfg, done, program, has, token, push, jump, stk, unary,
    List.replicate_succ, Function.update] <;>
    (funext k; cases k <;> simp [stk, unary, List.replicate_succ, Function.update]))

private theorem walk_end (t r g : ℕ) :
    step (cfg .walk [] t r g 0 0 []) =
      some (cfg .clearGap [] t r g 0 0 []) := by
  (simp [cfg, done, program, has, token, push, jump, stk, unary,
    List.replicate_succ, Function.update] <;>
    (funext k; cases k <;> simp [stk, unary, List.replicate_succ, Function.update]))

private def resetRun (xs : Bits) (t r g : ℕ) :
    Run (cfg .reset xs t r g 0 0 [])
      (cfg .walk xs t 0 (g + r + 2) 0 0 []) (r + 1) := by
  induction r generalizing g with
  | zero => exact one (by (simp [cfg, done, program, has, token, push, jump, stk, unary,
    List.replicate_succ, Function.update] <;>
    (funext k; cases k <;> simp [stk, unary, List.replicate_succ, Function.update])))
  | succ r ih =>
    have h : step (cfg .reset xs t (r + 1) g 0 0 []) =
        some (cfg .reset xs t r (g + 1) 0 0 []) := by (simp [cfg, done, program, has, token, push, jump, stk, unary,
    List.replicate_succ, Function.update] <;>
    (funext k; cases k <;> simp [stk, unary, List.replicate_succ, Function.update]))
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      seq (one h) (ih (g + 1))

private def clearGapRun (t r g a b : ℕ) (out : Bits) :
    Run (cfg .clearGap [] t r g a b out)
      (cfg .compare [] t r 0 a b out) (g + 1) := by
  induction g with
  | zero => exact one (by (simp [cfg, done, program, has, token, push, jump, stk, unary,
    List.replicate_succ, Function.update] <;>
    (funext k; cases k <;> simp [stk, unary, List.replicate_succ, Function.update])))
  | succ g ih =>
    have h : step (cfg .clearGap [] t r (g + 1) a b out) =
        some (cfg .clearGap [] t r g a b out) := by (simp [cfg, done, program, has, token, push, jump, stk, unary,
    List.replicate_succ, Function.update] <;>
    (funext k; cases k <;> simp [stk, unary, List.replicate_succ, Function.update]))
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using seq (one h) ih

private theorem unary_append_token (n : ℕ) (out : Bits) :
    unary n ++ true :: out = unary (n + 1) ++ out := by
  simp [unary, List.replicate_add, List.append_assoc]

private def emitFirstRun (a : ℕ) (out : Bits) :
    Run (cfg .emitFirst [] 0 0 0 a 0 out)
      (done (unary a ++ out)) (a + 1) := by
  induction a generalizing out with
  | zero => exact one (by (simp [cfg, done, program, has, token, push, jump, stk, unary,
    List.replicate_succ, Function.update] <;>
    (funext k; cases k <;> simp [stk, unary, List.replicate_succ, Function.update])))
  | succ a ih =>
    have h : step (cfg .emitFirst [] 0 0 0 (a + 1) 0 out) =
        some (cfg .emitFirst [] 0 0 0 a 0 (true :: out)) := by (simp [cfg, done, program, has, token, push, jump, stk, unary,
    List.replicate_succ, Function.update] <;>
    (funext k; cases k <;> simp [stk, unary, List.replicate_succ, Function.update]))
    simpa [unary_append_token, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      seq (one h) (ih (true :: out))

private def emitSecondRun (a b : ℕ) (out : Bits) :
    Run (cfg .emitSecond [] 0 0 0 a b out)
      (done (unary a ++ false :: (unary b ++ out))) (a + b + 2) := by
  induction b generalizing out with
  | zero =>
    have h : step (cfg .emitSecond [] 0 0 0 a 0 out) =
        some (cfg .emitFirst [] 0 0 0 a 0 (false :: out)) := by (simp [cfg, done, program, has, token, push, jump, stk, unary,
    List.replicate_succ, Function.update] <;>
    (funext k; cases k <;> simp [stk, unary, List.replicate_succ, Function.update]))
    simpa [unary, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      seq (one h) (emitFirstRun a (false :: out))
  | succ b ih =>
    have h : step (cfg .emitSecond [] 0 0 0 a (b + 1) out) =
        some (cfg .emitSecond [] 0 0 0 a b (true :: out)) := by (simp [cfg, done, program, has, token, push, jump, stk, unary,
    List.replicate_succ, Function.update] <;>
    (funext k; cases k <;> simp [stk, unary, List.replicate_succ, Function.update]))
    simpa [unary_append_token, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      seq (one h) (ih (true :: out))

/-- The two terminated unary fields used by the HILL advice encoding. -/
def pairFields (a b : ℕ) : Bits := encAdvice a b []

/-- Decode the input length, without assuming that its bits are all `true`. -/
def decodeWord (w : Bits) : Bits :=
  pairFields (Nat.unpair w.length).1 (Nat.unpair w.length).2

private def moveRemainderRun (r a b : ℕ) :
    Run (cfg .moveRemainder [] 0 r 0 a b [])
      (done (pairFields a (b + r))) (a + b + 2 * r + 3) := by
  induction r generalizing b with
  | zero =>
    have h : step (cfg .moveRemainder [] 0 0 0 a b []) =
        some (cfg .emitSecond [] 0 0 0 a b [false]) := by (simp [cfg, done, program, has, token, push, jump, stk, unary,
    List.replicate_succ, Function.update] <;>
    (funext k; cases k <;> simp [stk, unary, List.replicate_succ, Function.update]))
    simpa [pairFields, encAdvice, enc, unary,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      seq (one h) (emitSecondRun a b [false])
  | succ r ih =>
    have h : step (cfg .moveRemainder [] 0 (r + 1) 0 a b []) =
        some (cfg .moveRemainder [] 0 r 0 a (b + 1) []) := by (simp [cfg, done, program, has, token, push, jump, stk, unary,
    List.replicate_succ, Function.update] <;>
    (funext k; cases k <;> simp [stk, unary, List.replicate_succ, Function.update]))
    have hr := seq (one h) (ih (b + 1))
    have hout : b + 1 + r = b + (r + 1) := by omega
    rw [hout] at hr
    exact relax hr (by omega)

private def moveRootRun (t a b : ℕ) :
    Run (cfg .moveRoot [] t 0 0 a b [])
      (done (pairFields a (b + t))) (a + b + 2 * t + 3) := by
  induction t generalizing b with
  | zero =>
    have h : step (cfg .moveRoot [] 0 0 0 a b []) =
        some (cfg .emitSecond [] 0 0 0 a b [false]) := by (simp [cfg, done, program, has, token, push, jump, stk, unary,
    List.replicate_succ, Function.update] <;>
    (funext k; cases k <;> simp [stk, unary, List.replicate_succ, Function.update]))
    simpa [pairFields, encAdvice, enc, unary,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      seq (one h) (emitSecondRun a b [false])
  | succ t ih =>
    have h : step (cfg .moveRoot [] (t + 1) 0 0 a b []) =
        some (cfg .moveRoot [] t 0 0 a (b + 1) []) := by (simp [cfg, done, program, has, token, push, jump, stk, unary,
    List.replicate_succ, Function.update] <;>
    (funext k; cases k <;> simp [stk, unary, List.replicate_succ, Function.update]))
    have hr := seq (one h) (ih (b + 1))
    have hout : b + 1 + t = b + (t + 1) := by omega
    rw [hout] at hr
    exact relax hr (by omega)

private def clearSecondRun (r a b : ℕ) :
    Run (cfg .clearSecond [] 0 r 0 a b [])
      (cfg .moveRemainder [] 0 r 0 a 0 []) (b + 1) := by
  induction b with
  | zero => exact one (by (simp [cfg, done, program, has, token, push, jump, stk, unary,
    List.replicate_succ, Function.update] <;>
    (funext k; cases k <;> simp [stk, unary, List.replicate_succ, Function.update])))
  | succ b ih =>
    have h : step (cfg .clearSecond [] 0 r 0 a (b + 1) []) =
        some (cfg .clearSecond [] 0 r 0 a b []) := by (simp [cfg, done, program, has, token, push, jump, stk, unary,
    List.replicate_succ, Function.update] <;>
    (funext k; cases k <;> simp [stk, unary, List.replicate_succ, Function.update]))
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using seq (one h) ih

private def compareFields (t r a b : ℕ) : Bits :=
  if r < t then pairFields (a + r) (b + t)
  else pairFields (a + t) (r - t)

private def compareRun (t r a b : ℕ) :
    Run (cfg .compare [] t r 0 a b [])
      (done (compareFields t r a b)) (5 * (t + r) + 2 * a + 2 * b + 10) := by
  induction t generalizing r a b with
  | zero =>
    have h : step (cfg .compare [] 0 r 0 a b []) =
        some (cfg .clearSecond [] 0 r 0 a b []) := by (simp [cfg, done, program, has, token, push, jump, stk, unary,
    List.replicate_succ, Function.update] <;>
    (funext k; cases k <;> simp [stk, unary, List.replicate_succ, Function.update]))
    have hr := seq (one h) (seq (clearSecondRun r a b) (moveRemainderRun r a 0))
    apply relax (by simpa [compareFields] using hr)
    omega
  | succ t ih =>
    cases r with
    | zero =>
      have h : step (cfg .compare [] (t + 1) 0 0 a b []) =
          some (cfg .moveRoot [] (t + 1) 0 0 a b []) := by (simp [cfg, done, program, has, token, push, jump, stk, unary,
    List.replicate_succ, Function.update] <;>
    (funext k; cases k <;> simp [stk, unary, List.replicate_succ, Function.update]))
      have hr := seq (one h) (moveRootRun (t + 1) a b)
      apply relax (by simpa [compareFields] using hr)
      omega
    | succ r =>
      have h : step (cfg .compare [] (t + 1) (r + 1) 0 a b []) =
          some (cfg .compare [] t r 0 (a + 1) (b + 1) []) := by (simp [cfg, done, program, has, token, push, jump, stk, unary,
    List.replicate_succ, Function.update] <;>
    (funext k; cases k <;> simp [stk, unary, List.replicate_succ, Function.update]))
      have hr := seq (one h) (ih r (a + 1) (b + 1))
      apply relax (by simpa [compareFields, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hr)
      omega

private theorem compareFields_decode (m t r g : ℕ)
    (hEq : t * t + r = m) (hGap : r + g = 2 * t) :
    compareFields t r 0 0 = pairFields (Nat.unpair m).1 (Nat.unpair m).2 := by
  have hp := decode_eq_unpair hEq (show r ≤ 2 * t by omega)
  by_cases hrt : r < t
  · simpa [compareFields, hrt] using
      congrArg (fun p : ℕ × ℕ => pairFields p.1 p.2) hp
  · simpa [compareFields, hrt] using
      congrArg (fun p : ℕ × ℕ => pairFields p.1 p.2) hp

private def finishRun (m t r g : ℕ)
    (hEq : t * t + r = m) (hGap : r + g = 2 * t) :
    Run (cfg .walk [] t r g 0 0 [])
      (done (pairFields (Nat.unpair m).1 (Nat.unpair m).2)) (20 * m + 32) := by
  have hr := seq (one (walk_end t r g))
    (seq (clearGapRun t r g 0 0 []) (compareRun t r 0 0))
  rw [compareFields_decode m t r g hEq hGap] at hr
  apply relax hr
  obtain ⟨ht, hr, hg⟩ := state_bounds hEq hGap
  omega

/-- The work stacks satisfy `t*t+r=m` and `r+g=2*t` after `m` input bits.
The proof consumes the remaining input and then proves the exact output. -/
private def decodeRun (xs : Bits) (m t r g : ℕ)
    (hEq : t * t + r = m) (hGap : r + g = 2 * t) :
    Run (cfg .walk xs t r g 0 0 [])
      (done (pairFields (Nat.unpair (m + xs.length)).1
        (Nat.unpair (m + xs.length)).2))
      ((xs.length + 1) * (20 * (m + xs.length) + 32)) := by
  induction xs generalizing m t r g with
  | nil => simpa using finishRun m t r g hEq hGap
  | cons bit xs ih =>
    obtain ⟨ht, hr, hg⟩ := state_bounds hEq hGap
    have hlen : m + 1 + xs.length = m + (bit :: xs).length := by
      simp [Nat.add_comm, Nat.add_left_comm]
    cases g with
    | zero =>
      obtain ⟨heq', hgap'⟩ := rollover_invariant hEq (show r = 2 * t by omega)
      have hreset := resetRun xs (t + 1) r 0
      simp only [Nat.zero_add] at hreset
      have hrun := seq (one (walk_rollover bit xs t r))
        (seq hreset (ih (m + 1) (t + 1) 0 (r + 2) heq' hgap'))
      rw [hlen] at hrun
      apply relax hrun
      simp only [List.length_cons]
      nlinarith
    | succ g =>
      obtain ⟨heq', hgap'⟩ := token_step_invariant hEq hGap
      have hrun := seq (one (walk_token bit xs t r g))
        (ih (m + 1) t (r + 1) g heq' hgap')
      rw [hlen] at hrun
      apply relax hrun
      simp only [List.length_cons]
      nlinarith

private def time : Polynomial ℕ :=
  (Polynomial.X + 1) * (Polynomial.C 20 * Polynomial.X + Polynomial.C 32)

private theorem cfg_eq {c d : Cfg} (hl : c.l = d.l) (hv : c.var = d.var)
    (hs : ∀ t, c.stk t = d.stk t) : c = d := by
  have he := funext hs
  cases c
  cases d
  cases hl
  cases hv
  cases he
  rfl

private theorem init_eq (w : Bits) :
    initList machine w = cfg .walk w 0 0 0 0 0 [] := by
  refine cfg_eq (c := initList machine w) (d := cfg .walk w 0 0 0 0 0 []) rfl rfl ?_
  intro t
  cases t <;> simp [machine, initList, cfg, stk, unary]

private theorem halt_eq (w : Bits) : haltList machine w = done w := by
  refine cfg_eq (c := haltList machine w) (d := done w) rfl rfl ?_
  intro t
  cases t <;> simp [machine, haltList, done, stk, unary]

/-- An explicit finite TM2 machine, with bound `(n+1)*(20*n+32)`,
computes the two unary fields of `Nat.unpair` of the input length. -/
theorem decodeWord_polytime : PolyTimeComputable decodeWord := by
  refine ⟨{
    tm := machine
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Equiv.refl Bool
    time := time
    outputsFun := ?_ }⟩
  intro w
  change Run (initList machine (w.map id)) (haltList machine ((decodeWord w).map id))
    (time.eval w.length)
  simpa only [List.map_id, init_eq, halt_eq, decodeWord, time, Polynomial.eval_mul,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_C,
    Nat.zero_add] using decodeRun w 0 0 0 0 (by omega) (by omega)

@[simp] theorem decodeWord_eq (w : Bits) :
    decodeWord w = encAdvice (Nat.unpair w.length).1 (Nat.unpair w.length).2 [] := rfl

theorem decodeWord_of_length_pair (w : Bits) (a b : ℕ)
    (h : w.length = Nat.pair a b) :
    decodeWord w = encAdvice a b [] := by
  simp [decodeWord, pairFields, h]

end

end HILL.PRG.UnpairMachine


/-! ## Source component: HILL416_ParityMachine.lean -/

set_option backward.isDefEq.respectTransparency.types false

/-!
A direct finite-state TM2 certificate for one affine binary row. The input is
an offset bit followed by interleaved coefficient/input pairs. An unmatched
final coefficient is ignored, so the machine is total on arbitrary bit strings.
The checked certificate uses the exact polynomial bound `Polynomial.X + 1`.
-/

namespace HILL.PRG.RowParityMachine

open Turing StateTransition

noncomputable section

def pairsValue (acc : Bool) : Bits → Bool
  | [] => acc
  | [_] => acc
  | c :: x :: rest => pairsValue (Bool.xor acc (c && x)) rest

def evaluate : Bits → Bits
  | [] => [false]
  | offset :: rest => [pairsValue offset rest]

def interleave (coeffs input : Bits) : Bits :=
  (coeffs.zip input).flatMap (fun p => [p.1, p.2])

inductive Tape
  | input | output
  deriving DecidableEq, Fintype

inductive Label
  | offset | coefficient | value (coefficient : Bool)
  deriving DecidableEq, Fintype

private abbrev Γ : Tape → Type := fun _ => Bool
private abbrev State := Bool × Option Bool
private abbrev Stmt := TM2.Stmt Γ Label State
private abbrev Cfg := TM2.Cfg Γ Label State

private def jump (acc : State → Bool) (l : Label) : Stmt :=
  .load (fun s => (acc s, none)) (.goto (fun _ => l))

private def finish : Stmt :=
  .push .output Prod.fst (.load (fun _ => (false, none)) .halt)

private def read (empty : Stmt) (bit : Bool → Stmt) : Stmt :=
  .pop .input (fun s b => (s.1, b))
    (.branch (fun s => s.2.isSome)
      (.branch (fun s => s.2.getD false) (bit true) (bit false)) empty)

private def program : Label → Stmt
  | .offset => read finish (fun b => jump (fun _ => b) .coefficient)
  | .coefficient => read finish (fun c => jump Prod.fst (.value c))
  | .value c => read finish (fun x => jump (fun s => Bool.xor s.1 (c && x)) .coefficient)

private abbrev step := TM2.step program

private def stk (input output : Bits) : Tape → Bits
  | .input => input
  | .output => output

private def cfg (l : Label) (acc : Bool) (input : Bits) : Cfg :=
  ⟨some l, (acc, none), stk input []⟩

private def done (b : Bool) : Cfg :=
  ⟨none, (false, none), stk [] [b]⟩

private def machine : FinTM2 where
  K := Tape
  k₀ := .input
  k₁ := .output
  Γ := Γ
  Λ := Label
  main := .offset
  σ := State
  initialState := (false, none)
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := program

private abbrev Run (x y : Cfg) (n : ℕ) := EvalsToInTime step x (some y) n

private def one {x y : Cfg} (h : step x = some y) : Run x y 1 :=
  ⟨⟨1, h⟩, le_rfl⟩

private def seq {a b c : Cfg} {m n : ℕ}
    (x : Run a b m) (y : Run b c n) : Run a c (m+n) :=
  ⟨(EvalsToInTime.trans _ _ _ _ _ _ x y).toEvalsTo,
    (Nat.add_le_add y.steps_le_m x.steps_le_m).trans_eq (Nat.add_comm _ _)⟩

private theorem offset_step (b acc : Bool) (rest : Bits) :
    step (cfg .offset acc (b :: rest)) = some (cfg .coefficient b rest) := by
  cases b <;> (simp [cfg, done, program, read, finish, jump, stk, Function.update] <;>
    (funext k; cases k <;> simp [stk, Function.update]))

private theorem coefficient_step (c acc : Bool) (rest : Bits) :
    step (cfg .coefficient acc (c :: rest)) = some (cfg (.value c) acc rest) := by
  cases c <;> (simp [cfg, done, program, read, finish, jump, stk, Function.update] <;>
    (funext k; cases k <;> simp [stk, Function.update]))

private theorem value_step (c x acc : Bool) (rest : Bits) :
    step (cfg (.value c) acc (x :: rest)) =
      some (cfg .coefficient (Bool.xor acc (c && x)) rest) := by
  cases x <;> (simp [cfg, done, program, read, finish, jump, stk, Function.update] <;>
    (funext k; cases k <;> simp [stk, Function.update]))

private theorem empty_step (l : Label) (acc : Bool) :
    step (cfg l acc []) = some (done acc) := by
  cases l <;> (simp [cfg, done, program, read, finish, jump, stk, Function.update] <;>
    (funext k; cases k <;> simp [stk, Function.update]))

private def pairsRun (w : Bits) (acc : Bool) :
    Run (cfg .coefficient acc w) (done (pairsValue acc w)) (w.length+1) := by
  induction w using List.twoStepInduction generalizing acc with
  | nil => exact one (empty_step .coefficient acc)
  | singleton c =>
    simpa [pairsValue] using
      seq (one (coefficient_step c acc [])) (one (empty_step (.value c) acc))
  | cons_cons c x rest ih _ =>
    simpa only [pairsValue, List.length_cons, Nat.add_comm, Nat.add_left_comm] using
      seq (seq (one (coefficient_step c acc (x :: rest)))
        (one (value_step c x acc rest))) (ih (Bool.xor acc (c && x)))

private def evaluateRun (w : Bits) :
    Run (cfg .offset false w) (done ((evaluate w).headD false)) (w.length+1) := by
  cases w with
  | nil => exact one (empty_step .offset false)
  | cons b rest =>
    simpa only [evaluate, List.headD_cons, List.length_cons, Nat.add_comm 1] using
      seq (one (offset_step b false rest)) (pairsRun rest b)

private theorem cfg_eq {c d : Cfg} (hl : c.l = d.l) (hv : c.var = d.var)
    (hs : ∀ t, c.stk t = d.stk t) : c = d := by
  have he := funext hs
  cases c
  cases d
  cases hl
  cases hv
  cases he
  rfl

private theorem init_eq (w : Bits) :
    initList machine w = cfg .offset false w := by
  refine cfg_eq rfl rfl ?_
  intro t
  cases t <;> simp [machine, initList, cfg, stk]

private theorem halt_eq (b : Bool) : haltList machine [b] = done b := by
  refine cfg_eq rfl rfl ?_
  intro t
  cases t <;> simp [machine, haltList, done, stk]

private theorem evaluate_singleton (w : Bits) : evaluate w = [(evaluate w).headD false] := by
  cases w <;> rfl

/-- A concrete linear-time TM2 certificate; no composition or iteration axiom is used. -/
theorem evaluate_polytime : PolyTimeComputable evaluate := by
  refine ⟨{
    tm := machine
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Equiv.refl Bool
    time := Polynomial.X + 1
    outputsFun := ?_ }⟩
  intro w
  change Run (initList machine (w.map id))
    (haltList machine ((evaluate w).map id))
    ((Polynomial.X + 1 : Polynomial ℕ).eval w.length)
  have hout : haltList machine (evaluate w) = done ((evaluate w).headD false) := by
    cases w with
    | nil => exact halt_eq false
    | cons b rest => exact halt_eq (pairsValue b rest)
  simpa only [List.map_id, init_eq, hout,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one] using evaluateRun w

private theorem parity_succ (n : ℕ) :
    ((n + 1) % 2 == 1) = !(n % 2 == 1) := by
  have h : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases h with h | h <;> simp [Nat.add_mod n 1 2, h]

private theorem ip_cons (a b : Bool) (x y : Bits) :
    ip (a :: x) (b :: y) = Bool.xor (a && b) (ip x y) := by
  cases a <;> cases b <;> simp [ip, List.zip_cons_cons]
  exact parity_succ _

theorem pairsValue_interleave (coeffs input : Bits) (acc : Bool) :
    pairsValue acc (interleave coeffs input) = Bool.xor acc (ip coeffs input) := by
  induction coeffs generalizing input acc with
  | nil => simp [interleave, pairsValue, ip]
  | cons c coeffs ih =>
    cases input with
    | nil => simp [interleave, pairsValue, ip]
    | cons x input =>
      simp only [interleave, List.zip_cons_cons, List.flatMap_cons,
        List.cons_append, List.nil_append, pairsValue, ip_cons]
      rw [show (coeffs.zip input).flatMap (fun p => [p.1, p.2]) = interleave coeffs input from rfl,
        ih]
      cases acc <;> cases c <;> cases x <;> cases ip coeffs input <;> rfl

/-- Exact correctness for an affine row, including zero-length and truncated inputs. -/
theorem evaluate_affine_row (offset : Bool) (coeffs input : Bits) :
    evaluate (offset :: interleave coeffs input) = [Bool.xor offset (ip coeffs input)] := by
  simp only [evaluate, pairsValue_interleave]

end

end HILL.PRG.RowParityMachine


/-! ## Source component: HILL416_HybridTape.lean -/

/-!
Finite random-tape identities for the HILL hybrid simulator.
This file depends only on the published HILL model and Mathlib. In particular,
it does not import the unavailable parts of the attached HILL development.
-/

namespace HILL.PRG.HybridTape

theorem mem_cube_length (w : Bits) (n : ℕ) :
    w ∈ cube n ↔ w.length = n := by
  constructor
  · intro hw
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hw
    exact List.length_ofFn
  · intro hw
    subst n
    exact Finset.mem_image.mpr ⟨w.get, Finset.mem_univ _, List.ofFn_get w⟩

theorem cube_nonempty (n : ℕ) : (cube n).Nonempty :=
  ⟨List.replicate n false, (mem_cube_length _ _).2 (List.length_replicate ..)⟩

theorem uniformProb_congr_on {α : Type*} [DecidableEq α]
    (S : Finset α) (P Q : α → Prop) [DecidablePred P] [DecidablePred Q]
    (h : ∀ x ∈ S, P x ↔ Q x) :
    uniformProb S P = uniformProb S Q := by
  unfold uniformProb
  rw [Finset.filter_congr h]

theorem uniformProb_image_of_injOn {α β : Type*}
    [DecidableEq α] [DecidableEq β]
    (S : Finset α) (f : α → β) (hf : Set.InjOn f (S : Set α))
    (P : β → Prop) [DecidablePred P] :
    uniformProb (S.image f) P = uniformProb S (fun x => P (f x)) := by
  have hf' : Set.InjOn f ((S.filter (fun x => P (f x))) : Set α) := by
    intro x hx y hy hxy
    exact hf (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1 hxy
  unfold uniformProb
  rw [Finset.filter_image, Finset.card_image_iff.mpr hf', Finset.card_image_iff.mpr hf]

theorem append_injOn (m n : ℕ) :
    Set.InjOn (fun q : Bits × Bits => q.1 ++ q.2)
      (((cube m).product (cube n)) : Set (Bits × Bits)) := by
  intro x hx y hy hxy
  have hx' := (mem_cube_length x.1 m).1 (Finset.mem_product.mp hx).1
  have hy' := (mem_cube_length y.1 m).1 (Finset.mem_product.mp hy).1
  obtain ⟨hl, hr⟩ := List.append_inj hxy (hx'.trans hy'.symm)
  exact Prod.ext hl hr

theorem cube_append_image (m n : ℕ) :
    ((cube m).product (cube n)).image (fun q : Bits × Bits => q.1 ++ q.2) =
      cube (m + n) := by
  ext w
  constructor
  · intro hw
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨hu, hv⟩ := Finset.mem_product.mp hq
    apply (mem_cube_length _ _).2
    simp only [List.length_append, (mem_cube_length _ _).1 hu, (mem_cube_length _ _).1 hv]
  · intro hw
    have hlen := (mem_cube_length w (m + n)).1 hw
    refine Finset.mem_image.mpr ⟨(w.take m, w.drop m), ?_, List.take_append_drop m w⟩
    apply Finset.mem_product.mpr
    constructor
    · apply (mem_cube_length _ _).2
      simp only [List.length_take, hlen, Nat.min_eq_left (Nat.le_add_right m n)]
    · apply (mem_cube_length _ _).2
      simp only [List.length_drop, hlen, Nat.add_sub_cancel_left]

/-- Two contiguous tape blocks are exactly independent uniform bit strings. -/
theorem uniformProb_split (m n : ℕ) (P : Bits → Bits → Prop)
    [DecidableRel P] :
    uniformProb (cube (m + n)) (fun r => P (r.take m) (r.drop m)) =
      uniformProb ((cube m).product (cube n)) (fun q => P q.1 q.2) := by
  classical
  rw [← cube_append_image m n]
  rw [uniformProb_image_of_injOn _ _ (append_injOn m n)]
  apply uniformProb_congr_on
  intro q hq
  have hlen := (mem_cube_length q.1 m).1 (Finset.mem_product.mp hq).1
  simp only [← hlen, List.take_left, List.drop_left]

theorem uniformProb_product_left {α β : Type*}
    [DecidableEq α] [DecidableEq β]
    (S : Finset α) (T : Finset β) (hT : T.Nonempty)
    (P : α → Prop) [DecidablePred P] :
    uniformProb (S.product T) (fun q => P q.1) = uniformProb S P := by
  have hfilter : (S.product T).filter (fun q => P q.1) = (S.filter P).product T := by
    ext q
    simp only [Finset.product_eq_sprod, Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨⟨hs, ht⟩, hp⟩
      exact ⟨⟨hs, hp⟩, ht⟩
    · rintro ⟨⟨hs, hp⟩, ht⟩
      exact ⟨⟨hs, ht⟩, hp⟩
  unfold uniformProb
  rw [hfilter]
  simp only [Finset.product_eq_sprod, Finset.card_product, Nat.cast_mul]
  exact mul_div_mul_right _ _ (Nat.cast_ne_zero.mpr hT.card_ne_zero)

/-- Extra independent padding is irrelevant to an event using only a prefix. -/
theorem uniformProb_take_add (m n : ℕ) (P : Bits → Prop) [DecidablePred P] :
    uniformProb (cube (m + n)) (fun r => P (r.take m)) = uniformProb (cube m) P := by
  have h := uniformProb_split m n (fun x _ => P x)
  exact h.trans (uniformProb_product_left _ _ (cube_nonempty n) P)

/-- The padding identity uses only a bound on the tape length, not its computability. -/
theorem uniformProb_take_of_le (m L : ℕ) (h : m ≤ L)
    (P : Bits → Prop) [DecidablePred P] :
    uniformProb (cube L) (fun r => P (r.take m)) = uniformProb (cube m) P := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  exact uniformProb_take_add m d P

def threeCubes (p q c : ℕ) : Finset ((Bits × Bits) × Bits) :=
  ((cube p).product (cube q)).product (cube c)

def appendThree (z : (Bits × Bits) × Bits) : Bits :=
  (z.1.1 ++ z.1.2) ++ z.2

theorem appendThree_injOn (p q c : ℕ) :
    Set.InjOn appendThree (threeCubes p q c : Set ((Bits × Bits) × Bits)) := by
  intro x hx y hy hxy
  obtain ⟨hx12, hx3⟩ := Finset.mem_product.mp hx
  obtain ⟨hy12, hy3⟩ := Finset.mem_product.mp hy
  have hxp := (mem_cube_length x.1.1 p).1 (Finset.mem_product.mp hx12).1
  have hxq := (mem_cube_length x.1.2 q).1 (Finset.mem_product.mp hx12).2
  have hyp := (mem_cube_length y.1.1 p).1 (Finset.mem_product.mp hy12).1
  have hyq := (mem_cube_length y.1.2 q).1 (Finset.mem_product.mp hy12).2
  obtain ⟨h12, h3⟩ := List.append_inj hxy
    (by simp only [List.length_append, hxp, hxq, hyp, hyq])
  exact Prod.ext (append_injOn p q hx12 hy12 h12) h3

theorem cube_appendThree_image (p q c : ℕ) :
    (threeCubes p q c).image appendThree = cube (p + q + c) := by
  ext w
  constructor
  · intro hw
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨hz12, hz3⟩ := Finset.mem_product.mp hz
    obtain ⟨hz1, hz2⟩ := Finset.mem_product.mp hz12
    apply (mem_cube_length _ _).2
    simp only [appendThree, List.length_append, (mem_cube_length _ _).1 hz1,
      (mem_cube_length _ _).1 hz2, (mem_cube_length _ _).1 hz3]
  · intro hw
    have hlen := (mem_cube_length w (p + q + c)).1 hw
    refine Finset.mem_image.mpr
      ⟨((w.take p, (w.drop p).take q), w.drop (p + q)), ?_, ?_⟩
    · apply Finset.mem_product.mpr
      constructor
      · apply Finset.mem_product.mpr
        constructor
        · apply (mem_cube_length _ _).2
          simp only [List.length_take, hlen]
          exact Nat.min_eq_left (by omega)
        · apply (mem_cube_length _ _).2
          simp only [List.length_take, List.length_drop, hlen]
          exact Nat.min_eq_left (by omega)
      · apply (mem_cube_length _ _).2
        simp only [List.length_drop, hlen, Nat.add_sub_cancel_left]
    · simp only [appendThree, List.append_assoc, List.drop_take_append_drop,
        List.take_append_drop]

theorem uniformProb_three_exact (p q c : ℕ) (P : Bits → Bits → Bits → Prop)
    [∀ x y z, Decidable (P x y z)] :
    uniformProb (cube (p + q + c))
        (fun r => P (r.take p) ((r.drop p).take q) ((r.drop (p + q)).take c)) =
      uniformProb (threeCubes p q c) (fun z => P z.1.1 z.1.2 z.2) := by
  classical
  rw [← cube_appendThree_image p q c]
  rw [uniformProb_image_of_injOn _ _ (appendThree_injOn p q c)]
  apply uniformProb_congr_on
  intro z hz
  obtain ⟨hz12, hz3⟩ := Finset.mem_product.mp hz
  obtain ⟨hz1, hz2⟩ := Finset.mem_product.mp hz12
  have hp := (mem_cube_length z.1.1 p).1 hz1
  have hq := (mem_cube_length z.1.2 q).1 hz2
  have hc := (mem_cube_length z.2 c).1 hz3
  have hpq : (z.1.1 ++ z.1.2).length = p + q := by
    simp only [List.length_append, hp, hq]
  have h1 : (appendThree z).take p = z.1.1 := by
    simp only [appendThree, List.append_assoc, ← hp, List.take_left]
  have h2 : ((appendThree z).drop p).take q = z.1.2 := by
    simp only [appendThree, List.append_assoc, ← hp, List.drop_left, ← hq, List.take_left]
  have h3 : ((appendThree z).drop (p + q)).take c = z.2 := by
    simp only [appendThree, ← hpq, List.drop_left, ← hc, List.take_length]
  simp only [h1, h2, h3]

/--
The two sampler seeds and the adversary's coins are independent, even when the
total tape length encodes extra noncomputable integer parameters.
-/
theorem uniformProb_three_slices (p q c L : ℕ) (h : p + q + c ≤ L)
    (P : Bits → Bits → Bits → Prop) [∀ x y z, Decidable (P x y z)] :
    uniformProb (cube L)
        (fun r => P (r.take p) ((r.drop p).take q) ((r.drop (p + q)).take c)) =
      uniformProb (threeCubes p q c) (fun z => P z.1.1 z.1.2 z.2) := by
  classical
  have hpad := uniformProb_take_of_le (p + q + c) L h
    (fun r => P (r.take p) ((r.drop p).take q) ((r.drop (p + q)).take c))
  have heq (r : Bits) :
      P ((r.take (p + q + c)).take p)
          (((r.take (p + q + c)).drop p).take q)
          (((r.take (p + q + c)).drop (p + q)).take c) ↔
        P (r.take p) ((r.drop p).take q) ((r.drop (p + q)).take c) := by
    simp only [List.drop_take, List.take_take]
    simp only [Nat.min_eq_left (show p ≤ p + q + c by omega),
      Nat.min_eq_left (show q ≤ p + q + c - p by omega),
      Nat.add_sub_cancel_left, Nat.min_self]
  have hcongr := uniformProb_congr_on (cube L) _ _ (fun r _ => heq r)
  exact hcongr.symm.trans (hpad.trans (uniformProb_three_exact p q c P))

/--
An exact acceptance identity once the concrete simulator is proved to obey its
run equation. This theorem introduces no machine-computability assumptions.
-/
theorem acceptProb_eq_three_of_run
    (A B : Adv) (n : ℕ) (sourceAdvice targetAdvice : ℕ → ℕ)
    (y : Bits) (p q : ℕ) (assemble : Bits → Bits → Bits)
    (hbudget : p + q + A.coins n ≤ B.coins n)
    (hrun : ∀ r ∈ cube (B.coins n),
      B.run (encAdvice n (sourceAdvice n) (y ++ r)) =
        A.run (encAdvice n (targetAdvice n)
          (assemble (r.take p) ((r.drop p).take q) ++
            (r.drop (p + q)).take (A.coins n)))) :
    acceptProb B n sourceAdvice y =
      uniformProb (threeCubes p q (A.coins n))
        (fun z => A.run (encAdvice n (targetAdvice n)
          (assemble z.1.1 z.1.2 ++ z.2)) = [true]) := by
  unfold acceptProb
  calc
    _ = uniformProb (cube (B.coins n))
        (fun r => A.run (encAdvice n (targetAdvice n)
          (assemble (r.take p) ((r.drop p).take q) ++
            (r.drop (p + q)).take (A.coins n))) = [true]) := by
      apply uniformProb_congr_on
      intro r hr
      rw [hrun r hr]
    _ = _ := uniformProb_three_slices p q (A.coins n) (B.coins n) hbudget
      (fun u v r => A.run (encAdvice n (targetAdvice n) (assemble u v ++ r)) = [true])

end HILL.PRG.HybridTape

end HILL416_MachineLemmas

section HILL416_WordCodecs

namespace HILL.PRG.WordCodecs

open MachineContracts CLRS.Chapter34.Turing.PolyBuilder

private def unquoteSpec : StatefulFlatMapSpec Bool Bool Bool where
  initial := false
  action dataBit bit := if dataBit then ([bit], false) else ([], bit)
  finish _ := []

/-- Drop word separators and undo the bit escaping in a framed stream. -/
def unquoteWords : Bits → Bits := rewriteStatefulFlatMap unquoteSpec

theorem unquoteWords_polytime : PolyTimeComputable unquoteWords :=
  ⟨statefulFlatMap_computableInPolyTime unquoteSpec⟩

private theorem unquote_quote (w suffix : Bits) :
    rewriteStatefulFlatMapFrom unquoteSpec false (quoteBits w ++ suffix) =
      w ++ rewriteStatefulFlatMapFrom unquoteSpec false suffix := by
  induction w with
  | nil => rfl
  | cons b rest ih =>
    change b :: rewriteStatefulFlatMapFrom unquoteSpec false (quoteBits rest ++ suffix) = _
    rw [ih]
    rfl

theorem unquoteWords_encodeWords (w : List Bits) :
    unquoteWords (encodeWords w) = w.flatten := by
  induction w with
  | nil => rfl
  | cons x xs ih =>
    rw [show encodeWords (x :: xs) = quoteBits x ++ false :: encodeWords xs by
      simp [encodeWords, List.append_assoc]]
    change rewriteStatefulFlatMapFrom unquoteSpec false
      (quoteBits x ++ false :: encodeWords xs) = x ++ xs.flatten
    rw [unquote_quote]
    exact congrArg (x ++ ·) ih

private def parameterSpec : StatefulFlatMapSpec Bool Bool Bool where
  initial := true
  action active bit := if active && bit then ([true], true) else ([], false)
  finish _ := []

/-- Read the first unary field. -/
def unaryParameter : Bits → Bits := rewriteStatefulFlatMap parameterSpec

theorem unaryParameter_polytime : PolyTimeComputable unaryParameter :=
  ⟨statefulFlatMap_computableInPolyTime parameterSpec⟩

private theorem parameterSpec_inactive (w : Bits) :
    rewriteStatefulFlatMapFrom parameterSpec false w = [] := by
  induction w with
  | nil => rfl
  | cons b rest ih => exact ih

private theorem parameterSpec_replicate (n : ℕ) (w : Bits) :
    rewriteStatefulFlatMapFrom parameterSpec true (List.replicate n true ++ w) =
      List.replicate n true ++ rewriteStatefulFlatMapFrom parameterSpec true w := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ]
    exact congrArg (true :: ·) ih

theorem unaryParameter_replicate (n : ℕ) (w : Bits) :
    unaryParameter (List.replicate n true ++ false :: w) = List.replicate n true := by
  unfold unaryParameter rewriteStatefulFlatMap
  change rewriteStatefulFlatMapFrom parameterSpec true
    (List.replicate n true ++ false :: _) = _
  rw [parameterSpec_replicate]
  change List.replicate n true ++ rewriteStatefulFlatMapFrom parameterSpec false _ = _
  simp [parameterSpec_inactive]

theorem unaryParameter_encAdvice (n a : ℕ) (w : Bits) :
    unaryParameter (encAdvice n a w) = List.replicate n true :=
  unaryParameter_replicate n (List.replicate a true ++ false :: w)

private def headerSpec (preserve : Bool) : StatefulFlatMapSpec (Fin 3) Bool Bool where
  initial := 0
  action mode bit :=
    if mode = 2 then (if preserve then [] else [bit], mode)
    else (if preserve then [bit] else [], if bit then mode else mode + 1)
  finish _ := []

/-- Keep one side of the split after the second unary field. -/
def splitAdviceHeader (preserve : Bool) : Bits → Bits :=
  rewriteStatefulFlatMap (headerSpec preserve)

theorem splitAdviceHeader_polytime (preserve : Bool) :
    PolyTimeComputable (splitAdviceHeader preserve) :=
  ⟨statefulFlatMap_computableInPolyTime (headerSpec preserve)⟩

private theorem headerSpec_replicate (preserve : Bool) (mode : Fin 3) (hn : mode ≠ 2)
    (n : ℕ) (w : Bits) :
    rewriteStatefulFlatMapFrom (headerSpec preserve) mode (List.replicate n true ++ w) =
      (if preserve then List.replicate n true else []) ++
        rewriteStatefulFlatMapFrom (headerSpec preserve) mode w := by
  induction n with
  | zero => cases preserve <;> rfl
  | succ n ih =>
    cases preserve <;>
      simp [List.replicate_succ, rewriteStatefulFlatMapFrom, headerSpec, hn] at ih ⊢ <;>
      rw [ih]

private theorem headerSpec_payload (preserve : Bool) (w : Bits) :
    rewriteStatefulFlatMapFrom (headerSpec preserve) 2 w = if preserve then [] else w := by
  induction w with
  | nil => cases preserve <;> rfl
  | cons b rest ih =>
    cases preserve <;>
      simp [rewriteStatefulFlatMapFrom, headerSpec] at ih ⊢ <;>
      rw [ih]

theorem splitAdviceHeader_encAdvice (preserve : Bool) (n a : ℕ) (w : Bits) :
    splitAdviceHeader preserve (encAdvice n a w) = if preserve then encAdvice n a [] else w := by
  unfold splitAdviceHeader rewriteStatefulFlatMap
  change rewriteStatefulFlatMapFrom (headerSpec preserve) 0
    (List.replicate n true ++ false :: (List.replicate a true ++ false :: w)) = _
  rw [headerSpec_replicate preserve 0 (by decide)]
  have hOne :
      rewriteStatefulFlatMapFrom (headerSpec preserve) 0
        (false :: (List.replicate a true ++ false :: w)) =
      (if preserve then [false] else []) ++
        rewriteStatefulFlatMapFrom (headerSpec preserve) 1 (List.replicate a true ++ false :: w) := by
    cases preserve <;> rfl
  have hTwo : rewriteStatefulFlatMapFrom (headerSpec preserve) 1 (false :: w) =
      (if preserve then [false] else []) ++
        rewriteStatefulFlatMapFrom (headerSpec preserve) 2 w := by
    cases preserve <;> rfl
  rw [hOne, headerSpec_replicate preserve 1 (by decide), hTwo, headerSpec_payload]
  cases preserve <;> simp [encAdvice, enc]

/-- Serial calls with the encoded inputs and unframed concatenated outputs. -/
theorem plainBatchCalls_of_batchCalls (hBatch : BatchCallsContract)
    (M : Bits → Bits) (hM : PolyTimeComputable M) :
    ∃ Q : Bits → Bits, PolyTimeComputable Q ∧
      ∀ n a (xs : List Bits),
        Q (encAdvice n a (encodeWords xs)) =
          (xs.map fun x => M (encAdvice n a x)).flatten := by
  obtain ⟨B, ⟨hB⟩, hEq⟩ := hBatch M hM
  obtain ⟨hU⟩ := unquoteWords_polytime
  refine ⟨unquoteWords ∘ B, Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch hB hU, ?_⟩
  intro n a ws
  rw [Function.comp_apply, hEq n a ws, unquoteWords_encodeWords]

end HILL.PRG.WordCodecs

end HILL416_WordCodecs

section HILL416_RepeatInput

namespace HILL.PRG

open CLRS.Chapter34.Turing.PolyBuilder WordCodecs
open Turing.TM2Comp

private def bitToFrame (b : Bool) : UnaryFrameSym := if b then .tick else .separator
private def frameToBit (s : UnaryFrameSym) : Bool := s == .tick

private theorem frameToBit_bitToFrame (b : Bool) : frameToBit (bitToFrame b) = b := by
  cases b <;> rfl

private def symbolMap {A B : Type} (f : A → B) : LoopBody A B :=
  ⟨fun x => [f x], fun _ => 1, fun _ => by simp⟩

private theorem symbolMap_apply {A B : Type} (f : A → B) (xs : List A) :
    xs.flatMap (symbolMap f).emit = xs.map f := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact congrArg (f x :: ·) ih

/-- Concatenate two complete outputs by running both evaluators on the same input. -/
theorem polytime_append {f g : Bits → Bits} (hf : PolyTimeComputable f)
    (hg : PolyTimeComputable g) : PolyTimeComputable (fun w => f w ++ g w) := by
  obtain ⟨F⟩ := hf
  obtain ⟨G⟩ := hg
  let encoder := boundedLoop_computableInPolyTime (symbolMap bitToFrame)
  let decoder := boundedLoop_computableInPolyTime (symbolMap frameToBit)
  let left := Classical.choice (TM2ComputableInPolyTime.comp_scratch F encoder)
  let right := Classical.choice (TM2ComputableInPolyTime.comp_scratch G encoder)
  let pair := unaryFrameSameInputConcat_computableInPolyTime left right
  have full := TM2ComputableInPolyTime.comp_scratch pair decoder
  have hRound (w : Bits) : (w.map bitToFrame).map frameToBit = w := by
    simp [List.map_map, Function.comp_def, frameToBit_bitToFrame]
  simpa only [Levin2003.PolyTimeComputable, Function.comp_def, symbolMap_apply, List.map_append, hRound]
    using full

theorem polytime_comp {f g : Bits → Bits} (hf : PolyTimeComputable f)
    (hg : PolyTimeComputable g) : PolyTimeComputable (g ∘ f) := by
  obtain ⟨F⟩ := hf
  obtain ⟨G⟩ := hg
  exact TM2ComputableInPolyTime.comp_scratch F G

private def terminateSpec : StatefulFlatMapSpec Unit Bool Bool where
  initial := ()
  action _ b := ([b], ())
  finish _ := [false]

private theorem terminateSpec_apply (w : Bits) :
    rewriteStatefulFlatMap terminateSpec w = w ++ [false] := by
  unfold rewriteStatefulFlatMap
  induction w with
  | nil => rfl
  | cons b rest ih =>
    change b :: rewriteStatefulFlatMapFrom terminateSpec () rest = b :: (rest ++ [false])
    exact congrArg (b :: ·) ih

theorem polytime_append_false : PolyTimeComputable (fun w : Bits => w ++ [false]) := by
  have he : PolyTimeComputable (rewriteStatefulFlatMap terminateSpec) :=
    ⟨statefulFlatMap_computableInPolyTime terminateSpec⟩
  exact (funext terminateSpec_apply) ▸ he

def unaryField (T : ℕ → ℕ) (w : Bits) : Bits :=
  List.replicate (T (unaryParameter w).length) true ++ [false]

theorem unaryField_polytime {T : ℕ → ℕ} (hT : PTimeParam T) :
    PolyTimeComputable (unaryField T) :=
  polytime_comp (polytime_comp unaryParameter_polytime hT.2) polytime_append_false

theorem unaryField_encAdvice (T : ℕ → ℕ) (n a : ℕ) (x : Bits) :
    unaryField T (encAdvice n a x) = List.replicate (T n) true ++ [false] := by
  simp only [unaryField, unaryParameter_encAdvice, List.length_replicate]

/-- Attach the computed block width and count to an input, ahead of its original header. -/
def prepareRepeatInput (T k : ℕ → ℕ) (w : Bits) : Bits :=
  unaryField T w ++ unaryField k w ++ w

theorem prepareRepeatInput_polytime {T k : ℕ → ℕ} (hT : PTimeParam T) (hk : PTimeParam k) :
    PolyTimeComputable (prepareRepeatInput T k) := by
  have hid : PolyTimeComputable (id : Bits → Bits) :=
    ⟨Turing.idComputableInPolyTime (id : Bits → List Bool)⟩
  exact polytime_append (polytime_append (unaryField_polytime hT) (unaryField_polytime hk)) hid

theorem prepareRepeatInput_encAdvice (T k : ℕ → ℕ) (n a : ℕ) (x : Bits) :
    prepareRepeatInput T k (encAdvice n a x) = encAdvice (T n) (k n) (encAdvice n a x) := by
  simp only [prepareRepeatInput, unaryField, unaryParameter_encAdvice, List.length_replicate]
  simp [encAdvice, enc, List.append_assoc]

end HILL.PRG

end HILL416_RepeatInput

section HILL416_BlockFormatter

set_option backward.isDefEq.respectTransparency.types false

namespace HILL.PRG.BlockFormatter

open Turing StateTransition MachineContracts

noncomputable section

inductive Tape
  | input | widthA | widthB | count | outRev | output
  deriving DecidableEq, Fintype

inductive HeaderField
  | width | count | parameter | advice
  deriving DecidableEq, Fintype

inductive Label
  | read (field : HeaderField)
  | next (side : Bool)
  | block (side : Bool)
  | clearInput | clearA | clearB | reverseOutput
  deriving DecidableEq, Fintype

private abbrev Γ : Tape → Type := fun _ => Bool
private abbrev Stmt := TM2.Stmt Γ Label (Option Bool)
private abbrev Cfg := TM2.Cfg Γ Label (Option Bool)

private def jump (label : Label) : Stmt := .load (fun _ => none) (.goto (fun _ => label))

private def write (t : Tape) (b : Bool) (next : Stmt) : Stmt := .push t (fun _ => b) next

private def pop (t : Tape) (empty : Stmt) (bit : Bool → Stmt) : Stmt :=
  .pop t (fun _ b => b)
    (.branch Option.isSome (.branch (fun b => b.getD false) (bit true) (bit false)) empty)

private def has (t : Tape) (empty item : Stmt) : Stmt := pop t empty (fun _ => item)

private def active (side : Bool) : Tape := if side then .widthB else .widthA

private def afterHeader : HeaderField → Label
  | .width => .read .count
  | .count => .read .parameter
  | .parameter => .read .advice
  | .advice => .next false

private def readTrue : HeaderField → Stmt
  | .width => write .widthA true (jump (.read .width))
  | .count => write .count true (jump (.read .count))
  | .parameter => write .outRev true (jump (.read .parameter))
  | .advice => write .outRev true (jump (.read .advice))

private def readEnd (field : HeaderField) : Stmt :=
  match field with
  | .width | .count => jump (afterHeader field)
  | .parameter | .advice => write .outRev false (jump (afterHeader field))

private def emitBit (b : Bool) (next : Stmt) : Stmt :=
  write .outRev true (write .outRev b next)

private def program : Label → Stmt
  | .read field => pop .input (readEnd field) (fun b => if b then readTrue field else readEnd field)
  | .next s => has .count (jump .clearInput) (jump (.block s))
  | .block s =>
    has (active s) (write .outRev false (jump (.next !s)))
      (write (active !s) true
        (pop .input (emitBit false (jump (.block s))) (fun b => emitBit b (jump (.block s)))))
  | .clearInput => has .input (jump .clearA) (jump .clearInput)
  | .clearA => has .widthA (jump .clearB) (jump .clearA)
  | .clearB => has .widthB (jump .reverseOutput) (jump .clearB)
  | .reverseOutput =>
    pop .outRev (.load (fun _ => none) .halt) (fun b => write .output b (jump .reverseOutput))

private abbrev step := TM2.step program

private def stk (input a b count rev out : Bits) : Tape → Bits
  | .input => input
  | .widthA => a
  | .widthB => b
  | .count => count
  | .outRev => rev
  | .output => out

private def cfg (l : Label) (input a b count rev out : Bits) : Cfg :=
  ⟨some l, none, stk input a b count rev out⟩

private def done (out : Bits) : Cfg := ⟨none, none, stk [] [] [] [] [] out⟩

private def bankCfg (l : Label) (side : Bool) (input live spare count rev : Bits) : Cfg :=
  if side then cfg l input spare live count rev [] else cfg l input live spare count rev []

private def machine : FinTM2 where
  K := Tape
  k₀ := .input
  k₁ := .output
  Γ := Γ
  Λ := Label
  main := .read .width
  σ := Option Bool
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := program

private abbrev Run (x y : Cfg) (n : ℕ) := EvalsToInTime step x (some y) n

private def one {x y : Cfg} (h : step x = some y) : Run x y 1 :=
  ⟨⟨1, h⟩, le_rfl⟩

private def seq {a b c : Cfg} {m n : ℕ} (x : Run a b m) (y : Run b c n) : Run a c (m+n) :=
  ⟨(EvalsToInTime.trans _ _ _ _ _ _ x y).toEvalsTo,
    (Nat.add_le_add y.steps_le_m x.steps_le_m).trans_eq (Nat.add_comm _ _)⟩

private def relax {a b : Cfg} {m n : ℕ} (h : Run a b m) (hle : m ≤ n) : Run a b n :=
  ⟨h.toEvalsTo, h.steps_le_m.trans hle⟩

private theorem read_width (xs a b count rev out : Bits) :
    step (cfg (.read .width) (true :: xs) a b count rev out) =
      some (cfg (.read .width) xs (true :: a) b count rev out) := by
  (simp [cfg, done, bankCfg, program, active, has, pop, write, jump, emitBit,
    readTrue, readEnd, afterHeader, stk, Function.update] <;>
    (funext k; cases k <;> simp [stk, Function.update]))

private theorem read_count (xs a b count rev out : Bits) :
    step (cfg (.read .count) (true :: xs) a b count rev out) =
      some (cfg (.read .count) xs a b (true :: count) rev out) := by
  (simp [cfg, done, bankCfg, program, active, has, pop, write, jump, emitBit,
    readTrue, readEnd, afterHeader, stk, Function.update] <;>
    (funext k; cases k <;> simp [stk, Function.update]))

private theorem copy_header (field : HeaderField) (hf : field = .parameter ∨ field = .advice)
    (xs a b count rev out : Bits) :
    step (cfg (.read field) (true :: xs) a b count rev out) =
      some (cfg (.read field) xs a b count (true :: rev) out) := by
  rcases hf with rfl | rfl <;> (simp [cfg, done, bankCfg, program, active, has, pop, write, jump, emitBit,
    readTrue, readEnd, afterHeader, stk, Function.update] <;>
    (funext k; cases k <;> simp [stk, Function.update]))

private theorem finish_header (field : HeaderField) (xs a b count rev out : Bits) :
    step (cfg (.read field) (false :: xs) a b count rev out) =
      some (cfg (afterHeader field) xs a b count
        (if field = .parameter ∨ field = .advice then false :: rev else rev) out) := by
  cases field <;> (simp [cfg, done, bankCfg, program, active, has, pop, write, jump, emitBit,
    readTrue, readEnd, afterHeader, stk, Function.update] <;>
    (funext k; cases k <;> simp [stk, Function.update]))

private theorem finish_missing_header (field : HeaderField) (a b count rev out : Bits) :
    step (cfg (.read field) [] a b count rev out) =
      some (cfg (afterHeader field) [] a b count
        (if field = .parameter ∨ field = .advice then false :: rev else rev) out) := by
  cases field <;> (simp [cfg, done, bankCfg, program, active, has, pop, write, jump, emitBit,
    readTrue, readEnd, afterHeader, stk, Function.update] <;>
    (funext k; cases k <;> simp [stk, Function.update]))

private theorem start_block (side : Bool) (input activeWidth inactiveWidth count rev : Bits) :
    step (bankCfg (.next side) side input activeWidth inactiveWidth (true :: count) rev) =
      some (bankCfg (.block side) side input activeWidth inactiveWidth count rev) := by
  cases side <;> (simp [cfg, done, bankCfg, program, active, has, pop, write, jump, emitBit,
    readTrue, readEnd, afterHeader, stk, Function.update] <;>
    (funext k; cases k <;> simp [stk, Function.update]))

private theorem emit_block_bit (side : Bool) (input live spare count rev : Bits) :
    step (bankCfg (.block side) side input (true :: live) spare count rev) =
      some (bankCfg (.block side) side input.tail live (true :: spare) count (input.headD false :: true :: rev)) := by
  cases side <;> cases input with
  | nil => (simp [cfg, done, bankCfg, program, active, has, pop, write, jump, emitBit,
    readTrue, readEnd, afterHeader, stk, Function.update] <;>
    (funext k; cases k <;> simp [stk, Function.update]))
  | cons b xs => cases b <;> (simp [cfg, done, bankCfg, program, active, has, pop, write, jump, emitBit,
    readTrue, readEnd, afterHeader, stk, Function.update] <;>
    (funext k; cases k <;> simp [stk, Function.update]))

private theorem end_block (side : Bool) (input spare count rev : Bits) :
    step (bankCfg (.block side) side input [] spare count rev) =
      some (bankCfg (.next !side) (!side) input spare [] count (false :: rev)) := by
  cases side <;> (simp [cfg, done, bankCfg, program, active, has, pop, write, jump, emitBit,
    readTrue, readEnd, afterHeader, stk, Function.update] <;>
    (funext k; cases k <;> simp [stk, Function.update]))

private def unary : Bits → ℕ × Bits
  | [] => (0, [])
  | false :: xs => (0, xs)
  | true :: xs => let q := unary xs; (q.1 + 1, q.2)

private theorem unary_size (x : Bits) : (unary x).1 + (unary x).2.length ≤ x.length := by
  induction x with
  | nil => rfl
  | cons b xs ih =>
    cases b <;> simp [unary]
    omega

private theorem unary_field (t : ℕ) (x : Bits) :
    unary (List.replicate t true ++ false :: x) = (t, x) := by
  induction t with
  | zero => rfl
  | succ t ih => simp [List.replicate_succ, unary, ih]

private theorem move_true (n : ℕ) (tail : Bits) :
    List.replicate n true ++ true :: tail = true :: (List.replicate n true ++ tail) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

private def readWidthRun (xs a b count rev out : Bits) :
    let q := unary xs
    Run (cfg (.read .width) xs a b count rev out)
      (cfg (.read .count) q.2 (List.replicate q.1 true ++ a) b count rev out) (q.1+1) := by
  induction xs generalizing a with
  | nil => exact one (finish_missing_header .width a b count rev out)
  | cons bit xs ih =>
    cases bit with
    | false => exact one (finish_header .width xs a b count rev out)
    | true =>
      simpa only [unary, List.replicate_succ, List.cons_append, move_true, Nat.add_comm 1 ((unary xs).1+1)] using
        seq (one (read_width xs a b count rev out)) (ih (true :: a))

private def readCountRun (xs a b count rev out : Bits) :
    let q := unary xs
    Run (cfg (.read .count) xs a b count rev out)
      (cfg (.read .parameter) q.2 a b (List.replicate q.1 true ++ count) rev out) (q.1+1) := by
  induction xs generalizing count with
  | nil => exact one (finish_missing_header .count a b count rev out)
  | cons bit xs ih =>
    cases bit with
    | false => exact one (finish_header .count xs a b count rev out)
    | true =>
      simpa only [unary, List.replicate_succ, List.cons_append, move_true, Nat.add_comm 1 ((unary xs).1+1)] using
        seq (one (read_count xs a b count rev out)) (ih (true :: count))

private def copyHeaderRun (field : HeaderField) (hf : field = .parameter ∨ field = .advice)
    (xs a b count rev out : Bits) :
    let q := unary xs
    Run (cfg (.read field) xs a b count rev out)
      (cfg (afterHeader field) q.2 a b count (false :: (List.replicate q.1 true ++ rev)) out) (q.1+1) := by
  induction xs generalizing rev with
  | nil => simpa [unary, hf] using one (finish_missing_header field a b count rev out)
  | cons bit xs ih =>
    cases bit with
    | false => simpa [unary, hf] using one (finish_header field xs a b count rev out)
    | true =>
      simpa only [unary, List.replicate_succ, List.cons_append, move_true, Nat.add_comm 1 ((unary xs).1+1)] using
        seq (one (copy_header field hf xs a b count rev out)) (ih (true :: rev))

/-- Take exactly `width` bits, supplying zeroes when a malformed input ends early. -/
private def readBlock : ℕ → Bits → Bits × Bits
  | 0, xs => ([], xs)
  | n + 1, xs =>
    let remaining := readBlock n xs.tail
    (xs.headD false :: remaining.1, remaining.2)

private theorem readBlock_length (n : ℕ) (xs : Bits) : (readBlock n xs).1.length = n := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih => simp [readBlock, ih]

private theorem readBlock_rest_length (n : ℕ) (xs : Bits) : (readBlock n xs).2.length ≤ xs.length := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih =>
    exact (ih xs.tail).trans (by cases xs <;> simp)

private theorem readBlock_append (xs tail : Bits) :
    readBlock xs.length (xs ++ tail) = (xs, tail) := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp [readBlock, ih]

private def blockRun (side : Bool) (n : ℕ) (xs spare count rev : Bits) :
    let q := readBlock n xs
    Run (bankCfg (.block side) side xs (List.replicate n true) spare count rev)
      (bankCfg (.next !side) (!side) q.2 (List.replicate n true ++ spare) [] count
        (false :: (quoteBits q.1).reverse ++ rev)) (n+1) := by
  induction n generalizing xs spare rev with
  | zero => exact one (end_block side xs spare count rev)
  | succ n ih =>
    simpa [readBlock, quoteBits, List.flatMap_cons, List.reverse_append, List.replicate_succ,
      move_true, List.append_assoc, Nat.add_comm, Nat.add_left_comm] using
      seq (one (emit_block_bit side xs (List.replicate n true) spare count rev))
        (ih xs.tail (true :: spare) (xs.headD false :: true :: rev))

private def drainInput (xs a b acc : Bits) :
    Run (cfg .clearInput xs a b [] acc []) (cfg .clearA [] a b [] acc []) (xs.length+1) := by
  induction xs with
  | nil => exact one (by (simp [cfg, done, bankCfg, program, active, has, pop, write, jump, emitBit,
    readTrue, readEnd, afterHeader, stk, Function.update] <;>
    (funext k; cases k <;> simp [stk, Function.update])))
  | cons bit xs ih =>
    have h : step (cfg .clearInput (bit::xs) a b [] acc []) =
        some (cfg .clearInput xs a b [] acc []) := by cases bit <;> (simp [cfg, done, bankCfg, program, active, has, pop, write, jump, emitBit,
    readTrue, readEnd, afterHeader, stk, Function.update] <;>
    (funext k; cases k <;> simp [stk, Function.update]))
    simpa [Nat.add_comm, Nat.add_left_comm] using seq (one h) ih

private def drainA (a b acc : Bits) :
    Run (cfg .clearA [] a b [] acc []) (cfg .clearB [] [] b [] acc []) (a.length+1) := by
  induction a with
  | nil => exact one (by (simp [cfg, done, bankCfg, program, active, has, pop, write, jump, emitBit,
    readTrue, readEnd, afterHeader, stk, Function.update] <;>
    (funext k; cases k <;> simp [stk, Function.update])))
  | cons bit xs ih =>
    have h : step (cfg .clearA [] (bit::xs) b [] acc []) =
        some (cfg .clearA [] xs b [] acc []) := by cases bit <;> (simp [cfg, done, bankCfg, program, active, has, pop, write, jump, emitBit,
    readTrue, readEnd, afterHeader, stk, Function.update] <;>
    (funext k; cases k <;> simp [stk, Function.update]))
    simpa [Nat.add_comm, Nat.add_left_comm] using seq (one h) ih

private def drainB (b acc : Bits) :
    Run (cfg .clearB [] [] b [] acc []) (cfg .reverseOutput [] [] [] [] acc []) (b.length+1) := by
  induction b with
  | nil => exact one (by (simp [cfg, done, bankCfg, program, active, has, pop, write, jump, emitBit,
    readTrue, readEnd, afterHeader, stk, Function.update] <;>
    (funext k; cases k <;> simp [stk, Function.update])))
  | cons bit xs ih =>
    have h : step (cfg .clearB [] [] (bit::xs) [] acc []) =
        some (cfg .clearB [] [] xs [] acc []) := by cases bit <;> (simp [cfg, done, bankCfg, program, active, has, pop, write, jump, emitBit,
    readTrue, readEnd, afterHeader, stk, Function.update] <;>
    (funext k; cases k <;> simp [stk, Function.update]))
    simpa [Nat.add_comm, Nat.add_left_comm] using seq (one h) ih

private def finalize (acc out : Bits) :
    Run (cfg .reverseOutput [] [] [] [] acc out) (done (acc.reverse ++ out)) (acc.length+1) := by
  induction acc generalizing out with
  | nil => exact one (by (simp [cfg, done, bankCfg, program, active, has, pop, write, jump, emitBit,
    readTrue, readEnd, afterHeader, stk, Function.update] <;>
    (funext k; cases k <;> simp [stk, Function.update])))
  | cons bit xs ih =>
    have h : step (cfg .reverseOutput [] [] [] [] (bit::xs) out) =
        some (cfg .reverseOutput [] [] [] [] xs (bit::out)) := by cases bit <;> (simp [cfg, done, bankCfg, program, active, has, pop, write, jump, emitBit,
    readTrue, readEnd, afterHeader, stk, Function.update] <;>
    (funext k; cases k <;> simp [stk, Function.update]))
    simpa [List.reverse_cons, List.append_assoc, Nat.add_comm, Nat.add_left_comm] using
      seq (one h) (ih (bit::out))

private def noMoreBlocks (side : Bool) (n : ℕ) (xs acc : Bits) :
    Run (bankCfg (.next side) side xs (List.replicate n true) [] [] acc)
      (done acc.reverse) (xs.length + n + acc.length + 5) := by
  cases side with
  | false =>
    let w := List.replicate n true
    have h : step (cfg (.next false) xs w [] [] acc []) =
        some (cfg .clearInput xs w [] [] acc []) := by (simp [cfg, done, bankCfg, program, active, has, pop, write, jump, emitBit,
    readTrue, readEnd, afterHeader, stk, Function.update] <;>
    (funext k; cases k <;> simp [stk, Function.update]))
    simpa [bankCfg, w, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      seq (seq (seq (seq (one h) (drainInput xs w [] acc)) (drainA w [] acc))
        (drainB [] acc)) (finalize acc [])
  | true =>
    let w := List.replicate n true
    have h : step (cfg (.next true) xs [] w [] acc []) =
        some (cfg .clearInput xs [] w [] acc []) := by (simp [cfg, done, bankCfg, program, active, has, pop, write, jump, emitBit,
    readTrue, readEnd, afterHeader, stk, Function.update] <;>
    (funext k; cases k <;> simp [stk, Function.update]))
    simpa [bankCfg, w, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      seq (seq (seq (seq (one h) (drainInput xs [] w acc)) (drainA [] w acc))
        (drainB w acc)) (finalize acc [])

private def blocks (width : ℕ) : ℕ → Bits → List Bits
  | 0, _ => []
  | count + 1, xs =>
    let q := readBlock width xs
    q.1 :: blocks width count q.2

private theorem blocks_flatten (width : ℕ) (ws : List Bits)
    (h : ∀ x ∈ ws, x.length = width) :
    blocks width ws.length ws.flatten = ws := by
  induction ws with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    have hRead := readBlock_append x xs.flatten
    rw [hx] at hRead
    simp [blocks, hRead, ht]

private theorem quote_length (w : Bits) : (quoteBits w).length = 2 * w.length := by
  induction w with
  | nil => rfl
  | cons b rest ih =>
    simp [quoteBits, Nat.mul_succ, Nat.add_comm]
    omega

private def blocksRun (side : Bool) (width count : ℕ) (xs acc : Bits) :
    Run (bankCfg (.next side) side xs (List.replicate width true) []
        (List.replicate count true) acc)
      (done (acc.reverse ++ encodeWords (blocks width count xs)))
      (count * (3*width+3) + xs.length + width + acc.length + 5) := by
  induction count generalizing side xs acc with
  | zero => simpa [blocks, encodeWords] using noMoreBlocks side width xs acc
  | succ count ih =>
    let q := readBlock width xs
    let acc' := false :: (quoteBits q.1).reverse ++ acc
    let counter := List.replicate count true
    have first := one (start_block side xs (List.replicate width true) [] counter acc)
    have middle : Run (bankCfg (.block side) side xs (List.replicate width true) [] counter acc)
        (bankCfg (.next !side) (!side) q.2 (List.replicate width true) [] counter acc') (width+1) := by
      simpa only [List.append_nil] using blockRun side width xs [] counter acc
    have hSize : acc'.length = acc.length + 2*width + 1 := by
      simp [acc', q, quote_length, readBlock_length, Nat.add_comm]
    have hOut : acc'.reverse = acc.reverse ++ quoteBits q.1 ++ [false] := by
      simp [acc', List.reverse_cons, List.reverse_append]
    have hRest : q.2.length ≤ xs.length := readBlock_rest_length width xs
    have hb :
        (1 + (width + 1)) + (count * (3*width+3) + q.2.length + width + acc'.length + 5) ≤
          (count+1) * (3*width+3) + xs.length + width + acc.length + 5 := by
      rw [Nat.add_mul, Nat.one_mul, hSize]
      omega
    simpa [blocks, encodeWords, counter, q, hOut, List.append_assoc, List.replicate_succ] using
      relax (seq (seq first middle) (ih (!side) q.2 acc')) hb


/-- Frame a fixed number of fixed-width seed words. The first two unary fields
give the width and count, and the next two are passed to the batch evaluator. -/
def format : Bits → Bits := fun w =>
  let t := unary w
  let k := unary t.2
  let n := unary k.2
  let a := unary n.2
  encAdvice n.1 a.1 (encodeWords (blocks t.1 k.1 a.2))

private def time : Polynomial ℕ :=
  ((Polynomial.X : Polynomial ℕ) + 1) * (Polynomial.C 3 * Polynomial.X + Polynomial.C 12)

set_option maxHeartbeats 1500000 in
private def formatRun (w : Bits) :
    Run (cfg (.read .width) w [] [] [] [] []) (done (format w)) (time.eval w.length) := by
  let T := unary w
  let K := unary T.2
  let N := unary K.2
  let A := unary N.2
  let revN := false :: List.replicate N.1 true
  let revA := false :: (List.replicate A.1 true ++ revN)
  have r₁ : Run (cfg (.read .width) w [] [] [] [] [])
      (cfg (.read .count) T.2 (List.replicate T.1 true) [] [] [] []) (T.1+1) := by
    simpa only [List.append_nil] using readWidthRun w [] [] [] [] []
  have r₂ : Run (cfg (.read .count) T.2 (List.replicate T.1 true) [] [] [] [])
      (cfg (.read .parameter) K.2 (List.replicate T.1 true) [] (List.replicate K.1 true) [] [])
      (K.1+1) := by
    simpa only [List.append_nil] using readCountRun T.2 (List.replicate T.1 true) [] [] [] []
  have r₃ : Run (cfg (.read .parameter) K.2 (List.replicate T.1 true) [] (List.replicate K.1 true) [] [])
      (cfg (.read .advice) N.2 (List.replicate T.1 true) [] (List.replicate K.1 true) revN [])
      (N.1+1) := by
    simpa only [afterHeader, N, revN, List.append_nil] using copyHeaderRun .parameter (Or.inl rfl)
      K.2 (List.replicate T.1 true) [] (List.replicate K.1 true) [] []
  have r₄ : Run (cfg (.read .advice) N.2 (List.replicate T.1 true) [] (List.replicate K.1 true) revN [])
      (bankCfg (.next false) false A.2 (List.replicate T.1 true) [] (List.replicate K.1 true) revA)
      (A.1+1) :=
    copyHeaderRun .advice (Or.inr rfl) N.2 (List.replicate T.1 true) [] (List.replicate K.1 true) revN []
  have hAppend (out : Bits) : revA.reverse ++ out = encAdvice N.1 A.1 out := by
    simp [encAdvice, enc, revA, revN, List.reverse_cons, List.reverse_append, List.append_assoc]
  have r₅ : Run (bankCfg (.next false) false A.2 (List.replicate T.1 true) []
        (List.replicate K.1 true) revA)
      (done (format w)) (K.1*(3*T.1+3) + A.2.length + T.1 + revA.length + 5) := by
    simpa only [format, T, K, N, A, hAppend] using blocksRun false T.1 K.1 A.2 revA
  have hT : T.1 + T.2.length ≤ w.length := unary_size w
  have hK : K.1 + K.2.length ≤ T.2.length := unary_size T.2
  have hN : N.1 + N.2.length ≤ K.2.length := unary_size K.2
  have hA : A.1 + A.2.length ≤ N.2.length := unary_size N.2
  have hLen : revA.length = N.1 + A.1 + 2 := by
    simp [revA, revN, Nat.add_comm]
    omega
  have hProd : K.1*(3*T.1+3) ≤ w.length*(3*w.length+3) :=
    Nat.mul_le_mul (by omega) (by omega)
  refine relax (seq (seq (seq (seq r₁ r₂) r₃) r₄) r₅) ?_
  simp only [time, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_one, Polynomial.eval_C]
  calc
    _ ≤ w.length * (3*w.length+3) + 4*w.length + 11 := by omega
    _ ≤ _ := by nlinarith

private theorem cfg_eq {c d : Cfg} (hl : c.l = d.l) (hv : c.var = d.var)
    (hs : ∀ t, c.stk t = d.stk t) : c = d := by
  have he := funext hs
  cases c
  cases d
  cases hl
  cases hv
  cases he
  rfl

private theorem init_eq (w : Bits) : initList machine w = cfg (.read .width) w [] [] [] [] [] := by
  refine cfg_eq (c := initList machine w) (d := cfg (.read .width) w [] [] [] [] []) rfl rfl ?_
  intro t
  cases t <;> simp [machine, initList, cfg, stk]

private theorem halt_eq (w : Bits) : haltList machine w = done w := by
  refine cfg_eq (c := haltList machine w) (d := done w) rfl rfl ?_
  intro t
  cases t <;> simp [machine, haltList, done, stk]

theorem format_polytime : PolyTimeComputable format := by
  refine ⟨{
    tm := machine
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Equiv.refl Bool
    time := time
    outputsFun := ?_ }⟩
  intro w
  change Run (initList machine (w.map id)) (haltList machine ((format w).map id))
    (time.eval w.length)
  simpa only [List.map_id, init_eq, halt_eq] using formatRun w

theorem format_encAdvice (t n a : ℕ) (ws : List Bits)
    (hLen : ∀ w ∈ ws, w.length = t) :
    format (encAdvice t ws.length (encAdvice n a ws.flatten)) =
      encAdvice n a (encodeWords ws) := by
  simp only [format, encAdvice, enc, unary_field]
  rw [blocks_flatten t ws hLen]

/-- A single-block request keeps the requested prefix and drops the surplus bits. -/
theorem format_prefix (t n a : ℕ) (w : Bits) (h : t ≤ w.length) :
    format (encAdvice t 1 (encAdvice n a w)) =
      encAdvice n a (encodeWords [w.take t]) := by
  simp only [format, encAdvice, enc, unary_field, blocks]
  have ht : (w.take t).length = t := by simp [List.length_take, Nat.min_eq_left h]
  have hRead := readBlock_append (w.take t) (w.drop t)
  rw [ht, List.take_append_drop] at hRead
  rw [hRead]

end

end HILL.PRG.BlockFormatter

end HILL416_BlockFormatter

section HILL416_PayloadSlices

namespace HILL.PRG

open WordCodecs MachineContracts CLRS.Chapter34.Turing.PolyBuilder

private def oneSpec : StatefulFlatMapSpec Unit Bool Bool where
  initial := ()
  action _ _ := ([], ())
  finish _ := [true]

private theorem oneSpec_apply (w : Bits) :
    rewriteStatefulFlatMap oneSpec w = [true] := by
  unfold rewriteStatefulFlatMap
  induction w with
  | nil => rfl
  | cons b rest ih => exact ih

theorem onePTimeParam : PTimeParam (fun _ => 1) := by
  refine ⟨by simpa using InterfaceConsequences.polyParam_one, ?_⟩
  have hw : PolyTimeComputable (rewriteStatefulFlatMap oneSpec) :=
    ⟨statefulFlatMap_computableInPolyTime oneSpec⟩
  exact (funext oneSpec_apply) ▸ hw

/-- Extract a fixed-width prefix of the payload using the certified block framer. -/
theorem payloadTake (p : ℕ → ℕ) (hp : PTimeParam p) :
    ∃ T : Bits → Bits, PolyTimeComputable T ∧
      ∀ n a x, p n ≤ List.length x → T (encAdvice n a x) = x.take (p n) := by
  let run := unquoteWords ∘ splitAdviceHeader false ∘
    BlockFormatter.format ∘ prepareRepeatInput p (fun _ => 1)
  have h1 := polytime_comp (prepareRepeatInput_polytime hp onePTimeParam) BlockFormatter.format_polytime
  have h2 := polytime_comp h1 (splitAdviceHeader_polytime false)
  refine ⟨run, polytime_comp h2 unquoteWords_polytime, ?_⟩
  intro n a x hx
  simp only [run, Function.comp_apply, prepareRepeatInput_encAdvice,
    BlockFormatter.format_prefix _ _ _ _ hx, splitAdviceHeader_encAdvice, Bool.false_eq_true,
    if_false, unquoteWords_encodeWords, List.flatten_cons, List.flatten_nil, List.append_nil]

private def reversePayload (w : Bits) : Bits :=
  splitAdviceHeader true w ++ (splitAdviceHeader false w).reverse

private theorem reverse_polytime : PolyTimeComputable (List.reverse : Bits → Bits) :=
  ⟨reverse_computableInPolyTime (Γ := Bool)⟩

private theorem reversePayload_polytime : PolyTimeComputable reversePayload :=
  polytime_append (splitAdviceHeader_polytime true)
    (polytime_comp (splitAdviceHeader_polytime false) reverse_polytime)

private theorem reversePayload_encAdvice (n a : ℕ) (x : Bits) :
    reversePayload (encAdvice n a x) = encAdvice n a x.reverse := by
  simp only [reversePayload, splitAdviceHeader_encAdvice, if_true, Bool.false_eq_true, if_false]
  simp [encAdvice, enc, List.append_assoc]

/-- Extract a fixed-width suffix of the payload, retaining the original order. -/
theorem payloadSuffix (p : ℕ → ℕ) (hp : PTimeParam p) :
    ∃ T : Bits → Bits, PolyTimeComputable T ∧
      ∀ n a x, p n ≤ List.length x →
        T (encAdvice n a x) = x.drop (x.length - p n) := by
  obtain ⟨T, hT, hEq⟩ := payloadTake p hp
  refine ⟨List.reverse ∘ T ∘ reversePayload,
    polytime_comp (polytime_comp reversePayload_polytime hT) reverse_polytime, ?_⟩
  intro n a x hx
  have hRev : p n ≤ x.reverse.length := by simpa using hx
  simp only [Function.comp_apply, reversePayload_encAdvice, hEq n a x.reverse hRev,
    List.reverse_take, List.reverse_reverse, List.length_reverse]

/-- Split out a designated field when its offset and width are certified lengths. -/
theorem payloadSlice (offset width : ℕ → ℕ) (ho : PTimeParam offset) (hw : PTimeParam width) :
    ∃ T : Bits → Bits, PolyTimeComputable T ∧
      ∀ n a x, offset n + width n ≤ List.length x →
        T (encAdvice n a x) = (x.drop (offset n)).take (width n) := by
  obtain ⟨P, hP, hEqP⟩ := payloadTake _ (parameterArithmetic offset width ho hw).1
  obtain ⟨S, hS, hEqS⟩ := payloadSuffix width hw
  let rebuild := fun w => splitAdviceHeader true w ++ P w
  refine ⟨S ∘ rebuild, polytime_comp (polytime_append (splitAdviceHeader_polytime true) hP) hS, ?_⟩
  intro n a x hx
  let front := x.take (offset n + width n)
  have hf : front.length = offset n + width n := by simp [front, List.length_take, Nat.min_eq_left hx]
  have hl : width n ≤ front.length := by omega
  have hh : rebuild (encAdvice n a x) = encAdvice n a front := by
    simp only [rebuild, splitAdviceHeader_encAdvice, if_true, hEqP _ _ _ hx, front]
    simp [encAdvice, enc, List.append_assoc]
  simp only [Function.comp_apply, hh, hEqS n a front hl, hf, Nat.add_sub_cancel_right, front,
    List.drop_take, Nat.add_sub_cancel_left]

end HILL.PRG

end HILL416_PayloadSlices

section HILL416_DynamicFields

namespace HILL.PRG

open WordCodecs ConstructionContracts CLRS.Chapter34.Turing.PolyBuilder

private def constantWordSpec (xs : Bits) : StatefulFlatMapSpec Unit Bool Bool where
  initial := ()
  action _ _ := ([], ())
  finish _ := xs

private theorem constantWord_apply (xs w : Bits) :
    rewriteStatefulFlatMap (constantWordSpec xs) w = xs := by
  induction w with
  | nil => rfl
  | cons b w ih => exact ih

theorem polytime_constWord (xs : Bits) : PolyTimeComputable (fun _ : Bits => xs) :=
  (funext (constantWord_apply xs)) ▸ ⟨statefulFlatMap_computableInPolyTime (constantWordSpec xs)⟩

theorem polytime_idWord : PolyTimeComputable (id : Bits → Bits) :=
  ⟨Turing.idComputableInPolyTime id⟩

/-- Remove one terminated unary field. -/
def dropUnary (w : Bits) : Bits := splitAdviceHeader false (false :: w)

theorem dropUnary_polytime : PolyTimeComputable dropUnary :=
  polytime_comp (polytime_append (polytime_constWord [false]) polytime_idWord)
    (splitAdviceHeader_polytime false)

theorem dropUnary_replicate (p : ℕ) (w : Bits) :
    dropUnary (List.replicate p true ++ false :: w) = w :=
  splitAdviceHeader_encAdvice false 0 p w

theorem dropUnary_encAdvice (n a : ℕ) (w : Bits) :
    dropUnary (encAdvice n a w) = List.replicate a true ++ false :: w :=
  dropUnary_replicate n (List.replicate a true ++ false :: w)

/-- Decode the packed advice field into two terminated unary fields. -/
def decodeAdviceWord : Bits → Bits :=
  UnpairMachine.decodeWord ∘ unaryParameter ∘ dropUnary

theorem decodeAdviceWord_polytime : PolyTimeComputable decodeAdviceWord :=
  polytime_comp (polytime_comp dropUnary_polytime unaryParameter_polytime)
    UnpairMachine.decodeWord_polytime

theorem decodeAdviceWord_encAdvice (n a j : ℕ) (w : Bits) :
    decodeAdviceWord (encAdvice n (Nat.pair a j) w) = encAdvice a j [] := by
  simp only [decodeAdviceWord, Function.comp_apply, dropUnary_encAdvice, unaryParameter_replicate]
  exact UnpairMachine.decodeWord_of_length_pair _ a j List.length_replicate

def adviceFirstField (w : Bits) : Bits := unaryParameter (decodeAdviceWord w) ++ [false]

theorem adviceFirstField_polytime : PolyTimeComputable adviceFirstField :=
  polytime_comp (polytime_comp decodeAdviceWord_polytime unaryParameter_polytime)
    polytime_append_false

theorem adviceFirstField_encAdvice (n a j : ℕ) (w : Bits) :
    adviceFirstField (encAdvice n (Nat.pair a j) w) = List.replicate a true ++ [false] := by
  simp only [adviceFirstField, decodeAdviceWord_encAdvice, unaryParameter_encAdvice]

def adviceSecondField : Bits → Bits := dropUnary ∘ decodeAdviceWord

theorem adviceSecondField_polytime : PolyTimeComputable adviceSecondField :=
  polytime_comp decodeAdviceWord_polytime dropUnary_polytime

theorem adviceSecondField_encAdvice (n a j : ℕ) (w : Bits) :
    adviceSecondField (encAdvice n (Nat.pair a j) w) = List.replicate j true ++ [false] := by
  simp only [adviceSecondField, Function.comp_apply, decodeAdviceWord_encAdvice,
    dropUnary_encAdvice]

/-- Keep the requested number of bits of the payload, with the width in the first field. -/
def takeUnary (w : Bits) : Bits :=
  unquoteWords (splitAdviceHeader false
    (BlockFormatter.format (unaryParameter w ++ [false, true, false, false, false] ++ dropUnary w)))

theorem takeUnary_polytime : PolyTimeComputable takeUnary :=
  polytime_comp (polytime_comp (polytime_comp
    (polytime_append (polytime_append unaryParameter_polytime
      (polytime_constWord [false, true, false, false, false])) dropUnary_polytime)
    BlockFormatter.format_polytime) (splitAdviceHeader_polytime false)) unquoteWords_polytime

theorem takeUnary_replicate (j : ℕ) (w : Bits) (h : j ≤ w.length) :
    takeUnary (List.replicate j true ++ false :: w) = w.take j := by
  simp only [takeUnary, unaryParameter_replicate, dropUnary_replicate]
  rw [show List.replicate j true ++ [false, true, false, false, false] ++ w =
    encAdvice j 1 (encAdvice 0 0 w) by simp [encAdvice, enc, List.append_assoc]]
  rw [BlockFormatter.format_prefix j 0 0 w h]
  simp only [splitAdviceHeader_encAdvice, Bool.false_eq_true, if_false,
    unquoteWords_encodeWords, List.flatten_cons, List.flatten_nil, List.append_nil]

/-- Rebuild the header with the first component of the packed advice and a new payload. -/
def unpackFirstInput (P : Bits → Bits) (w : Bits) : Bits :=
  (unaryParameter w ++ [false]) ++ (adviceFirstField w ++ P w)

theorem unpackFirstInput_polytime {P : Bits → Bits} (hP : PolyTimeComputable P) :
    PolyTimeComputable (unpackFirstInput P) :=
  polytime_append (polytime_comp unaryParameter_polytime polytime_append_false)
    (polytime_append adviceFirstField_polytime hP)

theorem unpackFirstInput_encAdvice (P : Bits → Bits) (n a j : ℕ) (w : Bits) :
    unpackFirstInput P (encAdvice n (Nat.pair a j) w) =
      encAdvice n a (P (encAdvice n (Nat.pair a j) w)) := by
  simp only [unpackFirstInput, unaryParameter_encAdvice, adviceFirstField_encAdvice]
  simp [encAdvice, enc, List.append_assoc]

end HILL.PRG

end HILL416_DynamicFields

section HILL416_CallTrace

/-!
A verified call to a TM2 subroutine leaves the caller's stacks and state intact.
The Mathlib output certificate also guarantees the callee's own scratch stacks
are empty at return.
-/

namespace Turing.TM2Call

open StateTransition

variable (tm : FinTM2) {K L σ : Type} (Γ : K → Type)

abbrev Alphabet : tm.K ⊕ K → Type := Sum.elim tm.Γ Γ

abbrev Stmt (L σ : Type) :=
  TM2.Stmt (Alphabet tm Γ) (tm.Λ ⊕ L) (tm.σ × σ)

abbrev Cfg (L σ : Type) :=
  TM2.Cfg (Alphabet tm Γ) (tm.Λ ⊕ L) (tm.σ × σ)

def stackUnion (S : ∀ k, List (tm.Γ k)) (R : ∀ k, List (Γ k)) :
    ∀ k, List (Alphabet tm Γ k)
  | .inl k => S k
  | .inr k => R k

variable {Γ}

def liftStmt (returnTo : L) : tm.Stmt → Stmt tm Γ L σ
  | .push k f s => .push (.inl k) (fun v => f v.1) (liftStmt returnTo s)
  | .peek k f s => .peek (.inl k) (fun v x => (f v.1 x, v.2)) (liftStmt returnTo s)
  | .pop k f s => .pop (.inl k) (fun v x => (f v.1 x, v.2)) (liftStmt returnTo s)
  | .load f s => .load (fun v => (f v.1, v.2)) (liftStmt returnTo s)
  | .branch f s t => .branch (fun v => f v.1) (liftStmt returnTo s) (liftStmt returnTo t)
  | .goto l => .goto (fun v => .inl (l v.1))
  | .halt => .goto (fun _ => .inr returnTo)

def liftCfg (returnTo : L) (callerState : σ) (R : ∀ k, List (Γ k)) (c : tm.Cfg) :
    Cfg tm Γ L σ where
  l := some (c.l.elim (.inr returnTo) Sum.inl)
  var := (c.var, callerState)
  stk := stackUnion tm Γ c.stk R

def program (returnTo : L) (caller : L → Stmt tm Γ L σ) :
    (tm.Λ ⊕ L) → Stmt tm Γ L σ
  | .inl l => liftStmt tm returnTo (tm.m l)
  | .inr l => caller l

variable [DecidableEq K]

private theorem stackUnion_update (S : ∀ k, List (tm.Γ k))
    (R : ∀ k, List (Γ k)) (k : tm.K) (value : List (tm.Γ k)) :
    Function.update (stackUnion tm Γ S R) (.inl k) value =
      stackUnion tm Γ (Function.update S k value) R := by
  funext j
  cases j with
  | inl j =>
    by_cases h : j = k
    · subst j
      simp [stackUnion, Function.update]
    · have h' : (Sum.inl j : tm.K ⊕ K) ≠ Sum.inl k := fun he => h (Sum.inl.inj he)
      simp [stackUnion, Function.update, h, h']
  | inr j => simp [stackUnion, Function.update]

private theorem stepAux_lift (returnTo : L) (callerState : σ) (R : ∀ k, List (Γ k))
    (s : tm.Stmt) (v : tm.σ) (S : ∀ k, List (tm.Γ k)) :
    TM2.stepAux (liftStmt tm returnTo s) (v, callerState) (stackUnion tm Γ S R) =
      liftCfg tm returnTo callerState R (TM2.stepAux s v S) := by
  induction s generalizing v S with
  | push k f s ih =>
    simp [liftStmt, TM2.stepAux]
    rw [stackUnion_update]
    exact ih v _
  | peek k f s ih =>
    simp only [liftStmt, TM2.stepAux.eq_2, stackUnion]
    exact ih _ S
  | pop k f s ih =>
    simp [liftStmt, TM2.stepAux, stackUnion]
    rw [stackUnion_update]
    exact ih _ _
  | load f s ih =>
    simp only [liftStmt, TM2.stepAux.eq_4]
    exact ih _ S
  | branch f s t ihs iht =>
    cases h : f v <;> simp [liftStmt, h, ihs, iht]
  | goto l => rfl
  | halt => rfl

private theorem step_lift (returnTo : L) (caller : L → Stmt tm Γ L σ)
    (callerState : σ) (R : ∀ k, List (Γ k)) (c : tm.Cfg) (hc : tm.step c ≠ none) :
    TM2.step (program tm returnTo caller) (liftCfg tm returnTo callerState R c) =
      Option.map (liftCfg tm returnTo callerState R) (tm.step c) := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => exact (hc rfl).elim
  | some l =>
    exact congrArg some (stepAux_lift tm returnTo callerState R (tm.m l) v S)

/-- Run one certified callee from its entry configuration to its return
continuation without consuming any extra TM2 steps or changing caller data. -/
def evalsTo_return (returnTo : L) (caller : L → Stmt tm Γ L σ)
    (callerState : σ) (R : ∀ k, List (Γ k))
    {input : List (tm.Γ tm.k₀)} {output : List (tm.Γ tm.k₁)} {bound : ℕ}
    (run : TM2OutputsInTime tm input (some output) bound) :
    EvalsToInTime (TM2.step (program tm returnTo caller))
      (liftCfg tm returnTo callerState R (initList tm input))
      (some (liftCfg tm returnTo callerState R (haltList tm output))) bound :=
  TM2Comp.evalsToInTime_lift (liftCfg tm returnTo callerState R) run rfl
    (step_lift tm returnTo caller callerState R)

end Turing.TM2Call

end HILL416_CallTrace

section HILL416_BatchMachine

set_option backward.isDefEq.respectTransparency.types false

namespace HILL.PRG.BatchMachine

noncomputable section

open Turing StateTransition MachineContracts

inductive Tape
  | input | header | savedPrefix | reversedWord | accumulator | output
  deriving DecidableEq, Fintype

inductive Label
  | readHeader (second : Bool)
  | scan | copyWord | copyPrefix | restorePrefix | collect
  | clearWord | clearPrefix | reverseOutput
  deriving DecidableEq, Fintype

structure Tapes where
  input : Bits := []
  header : Bits := []
  savedPrefix : Bits := []
  reversedWord : Bits := []
  accumulator : Bits := []
  output : Bits := []

def Tapes.stk (s : Tapes) : Tape → Bits
  | .input => s.input
  | .header => s.header
  | .savedPrefix => s.savedPrefix
  | .reversedWord => s.reversedWord
  | .accumulator => s.accumulator
  | .output => s.output

variable {M : Bits → Bits}
abbrev Witness (M : Bits → Bits) :=
  TM2ComputableInPolyTime (id : Bits → List Bool) (id : Bits → List Bool) M

variable (H : Witness M)

abbrev alphabet : H.tm.K ⊕ Tape → Type := TM2Call.Alphabet H.tm (fun _ : Tape => Bool)
abbrev Inst := TM2Call.Stmt H.tm (fun _ : Tape => Bool) Label (Option Bool)
abbrev Config := TM2Call.Cfg H.tm (fun _ : Tape => Bool) Label (Option Bool)

def jump (l : Label) : Inst H :=
  .load (fun v => (v.1, none)) (.goto (fun _ => .inr l))

def push (k : Tape) (b : Bool) (next : Inst H) : Inst H :=
  .push (.inr k) (fun _ => b) next

def pushInput (b : Bool) (next : Inst H) : Inst H :=
  .push (.inl H.tm.k₀) (fun _ => H.inputAlphabet.symm b) next

def popDecoded (k : H.tm.K ⊕ Tape) (read : alphabet H k → Bool)
    (empty : Inst H) (nonempty : Bool → Inst H) : Inst H :=
  .pop k (fun v x => (v.1, x.map read))
    (.branch (fun v => v.2.isSome)
      (.branch (fun v => v.2.getD false) (nonempty true) (nonempty false))
      empty)

def pop (k : Tape) (empty : Inst H) (nonempty : Bool → Inst H) : Inst H :=
  popDecoded H (.inr k) id empty nonempty

def enter : Inst H :=
  .load (fun _ => (H.tm.initialState, none)) (.goto (fun _ => .inl H.tm.main))

def exit : Inst H :=
  .load (fun _ => (H.tm.initialState, none)) .halt

def caller : Label → Inst H
  | .readHeader second =>
    pop H .input (jump H .clearWord) fun b =>
      push H .header b (jump H (if b then .readHeader second else if second then .scan else .readHeader true))
  | .scan =>
    pop H .input (jump H .clearWord) fun mark =>
      if mark then
        pop H .input (jump H .clearWord)
          (fun b => push H .reversedWord b (jump H .scan))
      else jump H .copyWord
  | .copyWord =>
    pop H .reversedWord (jump H .copyPrefix) fun b =>
      pushInput H b (jump H .copyWord)
  | .copyPrefix =>
    pop H .header (jump H .restorePrefix) fun b =>
      pushInput H b (push H .savedPrefix b (jump H .copyPrefix))
  | .restorePrefix =>
    pop H .savedPrefix (enter H) fun b =>
      push H .header b (jump H .restorePrefix)
  | .collect =>
    popDecoded H (.inl H.tm.k₁) H.outputAlphabet
      (push H .accumulator false (jump H .scan))
      (fun b => push H .accumulator true (push H .accumulator b (jump H .collect)))
  | .clearWord =>
    pop H .reversedWord (jump H .clearPrefix) (fun _ => jump H .clearWord)
  | .clearPrefix =>
    pop H .header (jump H .reverseOutput) (fun _ => jump H .clearPrefix)
  | .reverseOutput =>
    pop H .accumulator (exit H) (fun b => push H .output b (jump H .reverseOutput))

def program : H.tm.Λ ⊕ Label → Inst H := TM2Call.program H.tm .collect (caller H)

abbrev step : Config H → Option (Config H) := TM2.step (program H)

def emptyStk : ∀ k : H.tm.K, List (H.tm.Γ k) := fun _ => []

def inputStk (w : Bits) : ∀ k : H.tm.K, List (H.tm.Γ k) :=
  (initList H.tm (w.map H.inputAlphabet.symm)).stk

def outputStk (w : Bits) : ∀ k : H.tm.K, List (H.tm.Γ k) :=
  (haltList H.tm (w.map H.outputAlphabet.symm)).stk

def config (l : Option (H.tm.Λ ⊕ Label)) (s : Tapes)
    (callee : ∀ k : H.tm.K, List (H.tm.Γ k)) : Config H where
  l := l
  var := (H.tm.initialState, none)
  stk := TM2Call.stackUnion H.tm (fun _ : Tape => Bool) callee s.stk

abbrev atLabel (l : Label) (s : Tapes) (callee : ∀ k : H.tm.K, List (H.tm.Γ k)) :
    Config H :=
  config H (some (.inr l)) s callee

def machine : FinTM2 := by
  letI := H.tm.kFin
  letI := H.tm.ΛFin
  letI := H.tm.σFin
  exact
    { K := H.tm.K ⊕ Tape
      k₀ := .inr .input
      k₁ := .inr .output
      Γ := alphabet H
      Λ := H.tm.Λ ⊕ Label
      main := .inr (.readHeader false)
      σ := H.tm.σ × Option Bool
      initialState := (H.tm.initialState, none)
      Γk₀Fin := inferInstanceAs (Fintype Bool)
      m := program H }

private def Tapes.set (s : Tapes) (t : Tape) (w : Bits) : Tapes :=
  match t with
  | .input => {s with input := w}
  | .header => {s with header := w}
  | .savedPrefix => {s with savedPrefix := w}
  | .reversedWord => {s with reversedWord := w}
  | .accumulator => {s with accumulator := w}
  | .output => {s with output := w}

private theorem update_right (s : Tapes) (t : Tape) (w : Bits)
    (callee : ∀ k : H.tm.K, List (H.tm.Γ k)) :
    Function.update (TM2Call.stackUnion H.tm (fun _ : Tape => Bool) callee s.stk)
      (.inr t) w =
    TM2Call.stackUnion H.tm (fun _ : Tape => Bool) callee (s.set t w).stk := by
  funext k
  cases k with
  | inl i => simp [Function.update, TM2Call.stackUnion]
  | inr i => cases t <;> cases i <;> simp [Function.update, TM2Call.stackUnion, Tapes.set, Tapes.stk]

private theorem update_left (s : Tapes) (t : H.tm.K) (w : List (H.tm.Γ t))
    (callee : ∀ k : H.tm.K, List (H.tm.Γ k)) :
    Function.update (TM2Call.stackUnion H.tm (fun _ : Tape => Bool) callee s.stk)
      (.inl t) w =
    TM2Call.stackUnion H.tm (fun _ : Tape => Bool) (Function.update callee t w) s.stk := by
  funext k
  cases k with
  | inl i =>
    by_cases hi : i = t
    · subst i
      simp [Function.update, TM2Call.stackUnion]
    · simp [Function.update, TM2Call.stackUnion, hi]
  | inr i => simp [Function.update, TM2Call.stackUnion]

@[simp] private theorem inputStk_here (w : Bits) :
    inputStk H w H.tm.k₀ = w.map H.inputAlphabet.symm := by simp [inputStk, initList]

@[simp] private theorem outputStk_here (w : Bits) :
    outputStk H w H.tm.k₁ = w.map H.outputAlphabet.symm := by simp [outputStk, haltList]

@[simp] private theorem inputStk_nil :
    inputStk H [] = emptyStk H := by
  funext k
  by_cases hk : k = H.tm.k₀
  · subst k; simp [emptyStk]
  · simp [inputStk, initList, hk, emptyStk]

@[simp] private theorem outputStk_nil :
    outputStk H [] = emptyStk H := by
  funext k
  by_cases hk : k = H.tm.k₁
  · subst k; simp [emptyStk]
  · simp [outputStk, haltList, hk, emptyStk]

private theorem inputStk_push (b : Bool) (w : Bits) :
    Function.update (inputStk H w) H.tm.k₀
      (H.inputAlphabet.symm b :: w.map H.inputAlphabet.symm) = inputStk H (b :: w) := by
  funext k
  by_cases hk : k = H.tm.k₀
  · subst k; simp [Function.update]
  · simp [Function.update, inputStk, initList, hk]

private theorem outputStk_pop (b : Bool) (w : Bits) :
    Function.update (outputStk H (b :: w)) H.tm.k₁
      (w.map H.outputAlphabet.symm) = outputStk H w := by
  funext k
  by_cases hk : k = H.tm.k₁
  · subst k; simp [Function.update]
  · simp [Function.update, outputStk, haltList, hk]

abbrev Run (c d : Config H) (n : ℕ) :=
  EvalsToInTime (step H) c (some d) n

private def one {c d : Config H} (he : step H c = some d) : Run H c d 1 :=
  ⟨⟨1, he⟩, le_rfl⟩

private def seq {c d e : Config H} {m n : ℕ} (h₁ : Run H c d m) (h₂ : Run H d e n) :
    Run H c e (m + n) :=
  ⟨(EvalsToInTime.trans _ _ _ _ _ _ h₁ h₂).toEvalsTo, by
    change h₂.steps + h₁.steps ≤ m + n
    simpa only [Nat.add_comm m n] using Nat.add_le_add h₂.steps_le_m h₁.steps_le_m⟩

private def relax {c d : Config H} {m n : ℕ} (h : Run H c d m) (hn : m ≤ n) :
    Run H c d n := ⟨h.toEvalsTo, h.steps_le_m.trans hn⟩

private theorem prefix_bit_step (second b : Bool) (xs : Bits) (s : Tapes)
    (callee : ∀ k : H.tm.K, List (H.tm.Γ k)) :
    step H (atLabel H (.readHeader second) {s with input := b :: xs} callee) =
      some (atLabel H (if b then .readHeader second else if second then .scan else .readHeader true)
        {s with input := xs, header := b :: s.header} callee) := by
  cases b <;> simp [program, config, TM2Call.program, caller, pop, popDecoded, push, jump,
    TM2Call.stackUnion, Tapes.stk, update_right, Tapes.set]

private theorem scan_bit_step (b : Bool) (xs : Bits) (s : Tapes)
    (callee : ∀ k : H.tm.K, List (H.tm.Γ k)) :
    step H (atLabel H .scan {s with input := true :: b :: xs} callee) =
      some (atLabel H .scan {s with input := xs, reversedWord := b :: s.reversedWord} callee) := by
  cases b <;> simp [program, config, TM2Call.program, caller, pop, popDecoded, push, jump,
    TM2Call.stackUnion, Tapes.stk, update_right, Tapes.set]

private theorem empty_update (t : H.tm.K) :
    Function.update (emptyStk H) t [] = emptyStk H := by
  funext k
  by_cases hk : k = t
  · subst k
    simp [Function.update, emptyStk]
  · simp [Function.update, hk]

private theorem prefix_end_step (second : Bool) (s : Tapes)
    (callee : ∀ k : H.tm.K, List (H.tm.Γ k)) :
    step H (atLabel H (.readHeader second) {s with input := []} callee) =
      some (atLabel H .clearWord {s with input := []} callee) := by
  simp [program, config, TM2Call.program, caller, pop, popDecoded, push, pushInput,
    jump, enter, exit, TM2Call.stackUnion, Tapes.stk, update_left, update_right, Tapes.set,
    inputStk_push, outputStk_pop, emptyStk, empty_update]

private theorem scan_end_step (s : Tapes) (rest : Bits)
    (ht : rest = [] ∨ rest = [true]) :
    step H (atLabel H .scan {s with input := rest} (emptyStk H)) =
      some (atLabel H .clearWord {s with input := []} (emptyStk H)) := by
  rcases ht with rfl | rfl <;>
    (simp [program, config, TM2Call.program, caller, pop, popDecoded, push, pushInput,
      jump, enter, exit, TM2Call.stackUnion, Tapes.stk, update_left, update_right, Tapes.set,
      inputStk_push, outputStk_pop, emptyStk, empty_update])

private theorem scan_delimiter_step (s : Tapes) (xs : Bits) :
    step H (atLabel H .scan {s with input := false :: xs} (emptyStk H)) =
      some (atLabel H .copyWord {s with input := xs} (emptyStk H)) := by
  simp [program, config, TM2Call.program, caller, pop, popDecoded, push, pushInput,
    jump, enter, exit, TM2Call.stackUnion, Tapes.stk, update_left, update_right, Tapes.set,
    inputStk_push, outputStk_pop, emptyStk, empty_update]

private theorem copy_word_step (s : Tapes) (b : Bool) (xs w : Bits) :
    step H (atLabel H .copyWord {s with reversedWord := b :: xs} (inputStk H w)) =
      some (atLabel H .copyWord {s with reversedWord := xs} (inputStk H (b :: w))) := by
  cases b <;>
    (simp [program, config, TM2Call.program, caller, pop, popDecoded, push, pushInput,
      jump, enter, exit, TM2Call.stackUnion, Tapes.stk, update_left, update_right, Tapes.set,
      inputStk_push, outputStk_pop, emptyStk, empty_update])

private theorem copy_word_end_step (s : Tapes) (w : Bits) :
    step H (atLabel H .copyWord {s with reversedWord := []} (inputStk H w)) =
      some (atLabel H .copyPrefix {s with reversedWord := []} (inputStk H w)) := by
  simp [program, config, TM2Call.program, caller, pop, popDecoded, push, pushInput,
    jump, enter, exit, TM2Call.stackUnion, Tapes.stk, update_left, update_right, Tapes.set,
    inputStk_push, outputStk_pop, emptyStk, empty_update]

private theorem copy_prefix_step (s : Tapes) (b : Bool) (xs w : Bits) :
    step H (atLabel H .copyPrefix {s with header := b :: xs} (inputStk H w)) =
      some (atLabel H .copyPrefix {s with header := xs, savedPrefix := b :: s.savedPrefix}
        (inputStk H (b :: w))) := by
  cases b <;>
    (simp [program, config, TM2Call.program, caller, pop, popDecoded, push, pushInput,
      jump, enter, exit, TM2Call.stackUnion, Tapes.stk, update_left, update_right, Tapes.set,
      inputStk_push, outputStk_pop, emptyStk, empty_update])

private theorem copy_prefix_end_step (s : Tapes) (w : Bits) :
    step H (atLabel H .copyPrefix {s with header := []} (inputStk H w)) =
      some (atLabel H .restorePrefix {s with header := []} (inputStk H w)) := by
  simp [program, config, TM2Call.program, caller, pop, popDecoded, push, pushInput,
    jump, enter, exit, TM2Call.stackUnion, Tapes.stk, update_left, update_right, Tapes.set,
    inputStk_push, outputStk_pop, emptyStk, empty_update]

private theorem restore_prefix_step (s : Tapes) (b : Bool) (xs w : Bits) :
    step H (atLabel H .restorePrefix {s with savedPrefix := b :: xs} (inputStk H w)) =
      some (atLabel H .restorePrefix {s with savedPrefix := xs, header := b :: s.header} (inputStk H w)) := by
  cases b <;>
    (simp [program, config, TM2Call.program, caller, pop, popDecoded, push, pushInput,
      jump, enter, exit, TM2Call.stackUnion, Tapes.stk, update_left, update_right, Tapes.set,
      inputStk_push, outputStk_pop, emptyStk, empty_update])

private theorem restore_prefix_end_step (s : Tapes) (w : Bits) :
    step H (atLabel H .restorePrefix {s with savedPrefix := []} (inputStk H w)) =
      some (config H (some (.inl H.tm.main)) {s with savedPrefix := []} (inputStk H w)) := by
  simp [program, config, TM2Call.program, caller, pop, popDecoded, push, pushInput,
    jump, enter, exit, TM2Call.stackUnion, Tapes.stk, update_left, update_right, Tapes.set,
    inputStk_push, outputStk_pop, emptyStk, empty_update]

private theorem collect_bit_step (s : Tapes) (b : Bool) (w : Bits) :
    step H (atLabel H .collect s (outputStk H (b :: w))) =
      some (atLabel H .collect {s with accumulator := b :: true :: s.accumulator} (outputStk H w)) := by
  cases b <;>
    (simp [program, config, TM2Call.program, caller, pop, popDecoded, push, pushInput,
      jump, enter, exit, TM2Call.stackUnion, Tapes.stk, update_left, update_right, Tapes.set,
      inputStk_push, outputStk_pop, emptyStk, empty_update])

private theorem collect_end_step (s : Tapes) :
    step H (atLabel H .collect s (outputStk H [])) =
      some (atLabel H .scan {s with accumulator := false :: s.accumulator} (emptyStk H)) := by
  simp [program, config, TM2Call.program, caller, pop, popDecoded, push, pushInput,
    jump, enter, exit, TM2Call.stackUnion, Tapes.stk, update_left, update_right, Tapes.set,
    inputStk_push, outputStk_pop, emptyStk, empty_update]

private theorem clear_word_step (s : Tapes) (b : Bool) (w : Bits) :
    step H (atLabel H .clearWord {s with reversedWord := b :: w} (emptyStk H)) =
      some (atLabel H .clearWord {s with reversedWord := w} (emptyStk H)) := by
  cases b <;>
    (simp [program, config, TM2Call.program, caller, pop, popDecoded, push, pushInput,
      jump, enter, exit, TM2Call.stackUnion, Tapes.stk, update_left, update_right, Tapes.set,
      inputStk_push, outputStk_pop, emptyStk, empty_update])

private theorem clear_word_end_step (s : Tapes) :
    step H (atLabel H .clearWord {s with reversedWord := []} (emptyStk H)) =
      some (atLabel H .clearPrefix {s with reversedWord := []} (emptyStk H)) := by
  simp [program, config, TM2Call.program, caller, pop, popDecoded, push, pushInput,
    jump, enter, exit, TM2Call.stackUnion, Tapes.stk, update_left, update_right, Tapes.set,
    inputStk_push, outputStk_pop, emptyStk, empty_update]

private theorem clear_prefix_step (s : Tapes) (b : Bool) (w : Bits) :
    step H (atLabel H .clearPrefix {s with header := b :: w} (emptyStk H)) =
      some (atLabel H .clearPrefix {s with header := w} (emptyStk H)) := by
  cases b <;>
    (simp [program, config, TM2Call.program, caller, pop, popDecoded, push, pushInput,
      jump, enter, exit, TM2Call.stackUnion, Tapes.stk, update_left, update_right, Tapes.set,
      inputStk_push, outputStk_pop, emptyStk, empty_update])

private theorem clear_prefix_end_step (s : Tapes) :
    step H (atLabel H .clearPrefix {s with header := []} (emptyStk H)) =
      some (atLabel H .reverseOutput {s with header := []} (emptyStk H)) := by
  simp [program, config, TM2Call.program, caller, pop, popDecoded, push, pushInput,
    jump, enter, exit, TM2Call.stackUnion, Tapes.stk, update_left, update_right, Tapes.set,
    inputStk_push, outputStk_pop, emptyStk, empty_update]

private theorem reverse_out_step (s : Tapes) (b : Bool) (w : Bits) :
    step H (atLabel H .reverseOutput {s with accumulator := b :: w} (emptyStk H)) =
      some (atLabel H .reverseOutput {s with accumulator := w, output := b :: s.output}
        (emptyStk H)) := by
  cases b <;>
    (simp [program, config, TM2Call.program, caller, pop, popDecoded, push, pushInput,
      jump, enter, exit, TM2Call.stackUnion, Tapes.stk, update_left, update_right, Tapes.set,
      inputStk_push, outputStk_pop, emptyStk, empty_update])

private theorem reverse_out_end_step (s : Tapes) :
    step H (atLabel H .reverseOutput {s with accumulator := []} (emptyStk H)) =
      some (config H none {s with accumulator := []} (emptyStk H)) := by
  simp [program, config, TM2Call.program, caller, pop, popDecoded, push, pushInput,
    jump, enter, exit, TM2Call.stackUnion, Tapes.stk, update_left, update_right, Tapes.set,
    inputStk_push, outputStk_pop, emptyStk, empty_update]

private def copyWordRun (s : Tapes) (word seed : Bits) :
    Run H (atLabel H .copyWord {s with reversedWord := word} (inputStk H seed))
      (atLabel H .copyPrefix {s with reversedWord := []} (inputStk H (word.reverse ++ seed)))
      (word.length + 1) := by
  induction word generalizing seed with
  | nil => exact one H (copy_word_end_step H s seed)
  | cons b rest ih =>
    simpa [List.reverse_cons, List.append_assoc, Nat.add_comm, Nat.add_left_comm] using
      seq H (one H (copy_word_step H s b rest seed)) (ih (b :: seed))

private def copyHeaderRun (s : Tapes) (header saved seed : Bits) :
    Run H (atLabel H .copyPrefix {s with header := header, savedPrefix := saved} (inputStk H seed))
      (atLabel H .restorePrefix {s with header := [], savedPrefix := header.reverse ++ saved}
        (inputStk H (header.reverse ++ seed)))
      (header.length + 1) := by
  induction header generalizing saved seed with
  | nil => exact one H (copy_prefix_end_step H {s with savedPrefix := saved} seed)
  | cons b rest ih =>
    simpa [List.reverse_cons, List.append_assoc, Nat.add_comm, Nat.add_left_comm] using
      seq H (one H (copy_prefix_step H {s with savedPrefix := saved} b rest seed))
        (ih (b :: saved) (b :: seed))

private def restoreHeaderRun (s : Tapes) (saved header seed : Bits) :
    Run H (atLabel H .restorePrefix {s with savedPrefix := saved, header := header} (inputStk H seed))
      (config H (some (.inl H.tm.main)) {s with savedPrefix := [], header := saved.reverse ++ header}
        (inputStk H seed))
      (saved.length + 1) := by
  induction saved generalizing header with
  | nil => exact one H (restore_prefix_end_step H {s with header := header} seed)
  | cons b rest ih =>
    simpa [List.reverse_cons, List.append_assoc, Nat.add_comm, Nat.add_left_comm] using
      seq H (one H (restore_prefix_step H {s with header := header} b rest seed)) (ih (b :: header))

private def callRun (s : Tapes) (seed : Bits) :
    Run H (config H (some (.inl H.tm.main)) s (inputStk H seed))
      (atLabel H .collect s (outputStk H (M seed))) (H.time.eval seed.length) :=
  by
    exact TM2Call.evalsTo_return H.tm (Γ := fun _ : Tape => Bool) Label.collect
      (caller H) (none : Option Bool) s.stk (H.outputsFun seed)

private def collectRun (s : Tapes) (w acc : Bits) :
    Run H (atLabel H .collect {s with accumulator := acc} (outputStk H w))
      (atLabel H .scan {s with accumulator := false :: ((quoteBits w).reverse ++ acc)}
        (emptyStk H))
      (w.length + 1) := by
  induction w generalizing acc with
  | nil => exact one H (collect_end_step H {s with accumulator := acc})
  | cons b rest ih =>
    simpa [quoteBits, List.flatMap_cons, List.reverse_append, List.append_assoc,
      Nat.add_comm, Nat.add_left_comm] using
      seq H (one H (collect_bit_step H {s with accumulator := acc} b rest))
        (ih (b :: true :: acc))

private def clearWordRun (s : Tapes) (w : Bits) :
    Run H (atLabel H .clearWord {s with reversedWord := w} (emptyStk H))
      (atLabel H .clearPrefix {s with reversedWord := []} (emptyStk H))
      (w.length + 1) := by
  induction w with
  | nil => exact one H (clear_word_end_step H s)
  | cons b rest ih =>
    simpa [Nat.add_comm, Nat.add_left_comm] using
      seq H (one H (clear_word_step H s b rest)) ih

private def clearHeaderRun (s : Tapes) (w : Bits) :
    Run H (atLabel H .clearPrefix {s with header := w} (emptyStk H))
      (atLabel H .reverseOutput {s with header := []} (emptyStk H))
      (w.length + 1) := by
  induction w with
  | nil => exact one H (clear_prefix_end_step H s)
  | cons b rest ih =>
    simpa [Nat.add_comm, Nat.add_left_comm] using
      seq H (one H (clear_prefix_step H s b rest)) ih

private def reverseOutputRun (s : Tapes) (w out : Bits) :
    Run H (atLabel H .reverseOutput {s with accumulator := w, output := out} (emptyStk H))
      (config H none {s with accumulator := [], output := w.reverse ++ out} (emptyStk H))
      (w.length + 1) := by
  induction w generalizing out with
  | nil => exact one H (reverse_out_end_step H {s with output := out})
  | cons b rest ih =>
    simpa [List.reverse_cons, List.append_assoc, Nat.add_comm, Nat.add_left_comm] using
      seq H (one H (reverse_out_step H {s with output := out} b rest))
        (ih (b :: out))

private def scanTapes (input header word acc : Bits) : Tapes where
  input := input
  header := header
  reversedWord := word
  accumulator := acc

private def scanCfg (input header word acc : Bits) : Config H :=
  atLabel H .scan (scanTapes input header word acc) (emptyStk H)

private def finalCfg (out : Bits) : Config H := config H none { output := out } (emptyStk H)

private def cleanup (header word acc : Bits) :
    Run H (atLabel H .clearWord (scanTapes [] header word acc) (emptyStk H))
      (finalCfg H acc.reverse) (word.length + header.length + acc.length + 3) := by
  let a := clearWordRun H (scanTapes [] header [] acc) word
  let b := clearHeaderRun H (scanTapes [] [] [] acc) header
  let c := reverseOutputRun H {} acc []
  simpa [finalCfg, scanTapes, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    seq H (seq H a b) c

private def callChunk (input header word acc : Bits) :
    let seed := header.reverse ++ word.reverse
    let y := M seed
    Run H (atLabel H .copyWord (scanTapes input header word acc) (emptyStk H))
      (scanCfg H input header [] (false :: ((quoteBits y).reverse ++ acc)))
      (word.length + 2 * header.length + H.time.eval seed.length + y.length + 4) := by
  dsimp only
  let a := copyWordRun H (scanTapes input header [] acc) word []
  let b := copyHeaderRun H (scanTapes input [] [] acc) header [] word.reverse
  let c := restoreHeaderRun H (scanTapes input [] [] acc) header.reverse [] (header.reverse ++ word.reverse)
  let d := callRun H (scanTapes input header [] acc) (header.reverse ++ word.reverse)
  let e := collectRun H (scanTapes input header [] []) (M (header.reverse ++ word.reverse)) acc
  have a' : Run H (atLabel H .copyWord (scanTapes input header word acc) (emptyStk H))
      (atLabel H .copyPrefix (scanTapes input header [] acc) (inputStk H word.reverse))
      (word.length + 1) := by
    simpa [scanTapes] using a
  have b' : Run H (atLabel H .copyPrefix (scanTapes input header [] acc) (inputStk H word.reverse))
      (atLabel H .restorePrefix {scanTapes input [] [] acc with savedPrefix := header.reverse}
        (inputStk H (header.reverse ++ word.reverse))) (header.length + 1) := by
    simpa [scanTapes] using b
  have c' : Run H (atLabel H .restorePrefix {scanTapes input [] [] acc with savedPrefix := header.reverse}
        (inputStk H (header.reverse ++ word.reverse)))
      (config H (some (.inl H.tm.main)) (scanTapes input header [] acc)
        (inputStk H (header.reverse ++ word.reverse))) (header.length + 1) := by
    simpa [scanTapes] using c
  have e' : Run H (atLabel H .collect (scanTapes input header [] acc)
        (outputStk H (M (header.reverse ++ word.reverse))))
      (scanCfg H input header [] (false :: ((quoteBits (M (header.reverse ++ word.reverse))).reverse ++ acc)))
      ((M (header.reverse ++ word.reverse)).length + 1) := by
    simpa [scanCfg, scanTapes] using e
  exact relax H (seq H (seq H (seq H (seq H a' b') c') d) e') (by omega)

/-- A truncated final word is ignored. Earlier complete words are still evaluated. -/
def decodeWordsAux : Bits → Bits → List Bits
  | [], _ => []
  | false :: rest, word => word.reverse :: decodeWordsAux rest []
  | [true], _ => []
  | true :: bit :: rest, word => decodeWordsAux rest (bit :: word)

@[simp] private theorem quoteBits_length (w : Bits) : (quoteBits w).length = 2 * w.length := by
  induction w with
  | nil => rfl
  | cons b rest ih =>
    simp [quoteBits, Nat.mul_succ, Nat.add_comm]
    omega

private def outputBound (L : ℕ) : ℕ :=
  L + Turing.TM2Comp.maxPushCount₁ H * H.time.eval L

private def scanBudget (L : ℕ) : ℕ := 6 + 2 * L + H.time.eval L + 3 * outputBound H L

private theorem scanBudget_ge (L : ℕ) : 6 ≤ scanBudget H L := by unfold scanBudget; omega

private theorem length_le_outputBound (seed : Bits) {L : ℕ} (h : seed.length ≤ L) :
    (M seed).length ≤ outputBound H L := by
  have hLen : (M seed).length ≤ seed.length + Turing.TM2Comp.maxPushCount₁ H *
      (H.outputsFun seed).toEvalsTo.steps := by
    simpa using Turing.TM2Comp.evalsTo_out_len_le H seed
  exact hLen.trans (Nat.add_le_add h (Nat.mul_le_mul_left _
    ((H.outputsFun seed).steps_le_m.trans (Turing.TM2Comp.Polynomial.eval_mono_nat h))))

set_option maxHeartbeats 1500000 in
private def scanRun (L : ℕ) (input header word acc : Bits)
    (hLen : header.length + word.length + input.length ≤ L) :
    Run H (scanCfg H input header word acc)
      (finalCfg H (acc.reverse ++
        encodeWords ((decodeWordsAux input word).map (fun w => M (header.reverse ++ w)))))
      ((input.length + 1) * scanBudget H L + header.length + word.length + acc.length) := by
  cases hi : input with
  | nil =>
    have hStep := one H (scan_end_step H (scanTapes [] header word acc) [] (Or.inl rfl))
    have tr := seq H hStep (cleanup H header word acc)
    have hCost := scanBudget_ge H L
    have hCost' : 1 + (word.length + header.length + acc.length + 3) ≤
        scanBudget H L + header.length + word.length + acc.length := by omega
    simpa [decodeWordsAux, encodeWords, scanCfg, scanTapes] using relax H tr hCost'
  | cons marker rest =>
    cases hm : marker with
    | false =>
      simp only [hi, hm, List.length_cons] at hLen
      let seed := header.reverse ++ word.reverse
      let y := M seed
      let acc' := false :: ((quoteBits y).reverse ++ acc)
      have hRest : header.length + ([] : Bits).length + rest.length ≤ L := by
        simp only [List.length_nil]
        omega
      have hSeed : seed.length ≤ L := by simp [seed]; omega
      have hTime := Turing.TM2Comp.Polynomial.eval_mono_nat (p := H.time) hSeed
      have hy : y.length ≤ outputBound H L := length_le_outputBound H seed hSeed
      have hHdr : header.length ≤ L := by omega
      have hAcc : acc'.length = acc.length + 2 * y.length + 1 := by
        simp [acc', Nat.add_comm]
      have hReversed : acc'.reverse = acc.reverse ++ quoteBits y ++ [false] := by
        simp [acc', List.reverse_cons, List.reverse_append]
      have hOne : Run H (scanCfg H (false :: rest) header word acc)
          (atLabel H .copyWord (scanTapes rest header word acc) (emptyStk H)) 1 :=
        one H (scan_delimiter_step H (scanTapes rest header word acc) rest)
      let start := seq H hOne (callChunk H rest header word acc)
      let cont := scanRun L rest header [] acc' hRest
      have hCost :
          (1 + (word.length + 2 * header.length + H.time.eval seed.length + y.length + 4)) +
            ((rest.length + 1) * scanBudget H L + header.length + ([] : Bits).length + acc'.length)
          ≤ ((false :: rest).length + 1) * scanBudget H L + header.length + word.length + acc.length := by
        simp only [List.length_cons, List.length_nil, Nat.add_mul, Nat.one_mul, hAcc]
        unfold scanBudget
        omega
      simpa [decodeWordsAux, encodeWords, seed, y, hReversed, List.append_assoc] using
        relax H (seq H start cont) hCost
    | true =>
      cases hr : rest with
      | nil =>
        have hStep := one H (scan_end_step H (scanTapes [] header word acc) [true] (Or.inr rfl))
        have tr := seq H hStep (cleanup H header word acc)
        have hCost := scanBudget_ge H L
        have hCost' : 1 + (word.length + header.length + acc.length + 3) ≤
            2 * scanBudget H L + header.length + word.length + acc.length := by omega
        simpa [decodeWordsAux, encodeWords, scanCfg, scanTapes] using relax H tr hCost'
      | cons b rest =>
        have hRest : header.length + (b :: word).length + rest.length ≤ L := by
          simp only [hi, hm, hr, List.length_cons] at hLen ⊢
          omega
        have hOne : Run H (scanCfg H (true :: b :: rest) header word acc)
            (scanCfg H rest header (b :: word) acc) 1 :=
          one H (scan_bit_step H b rest (scanTapes rest header word acc) (emptyStk H))
        let cont := scanRun L rest header (b :: word) acc hRest
        have hCost := scanBudget_ge H L
        exact relax H (seq H hOne cont) (by
          simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
          omega)
termination_by input.length
decreasing_by all_goals simp_all

/-- Read two unary fields and preserve exactly the consumed prefix. -/
def takeHeader : Bits → Bool → Bits × Option Bits
  | [], _ => ([], none)
  | bit :: rest, second =>
    if !bit && second then ([false], some rest)
    else
      let tail := takeHeader rest (second || !bit)
      (bit :: tail.1, tail.2)

private theorem takeHeader_length (w : Bits) (second : Bool) :
    (takeHeader w second).1.length + ((takeHeader w second).2.map List.length).getD 0 =
      w.length := by
  induction w generalizing second with
  | nil => rfl
  | cons b rest ih =>
    have ht := ih true
    have hf := ih false
    cases second <;> cases b <;> simp [takeHeader] <;> omega

private def headerResult (header : Bits) (rest : Option Bits) : Config H :=
  match rest with
  | none => atLabel H .clearWord (scanTapes [] header [] []) (emptyStk H)
  | some input => scanCfg H input header [] []

private def headerRun (w header : Bits) (second : Bool) :
    Run H (atLabel H (.readHeader second) (scanTapes w header [] []) (emptyStk H))
      (headerResult H ((takeHeader w second).1.reverse ++ header) (takeHeader w second).2)
      (w.length + 1) := by
  induction w generalizing second header with
  | nil => exact one H (prefix_end_step H second (scanTapes [] header [] []) (emptyStk H))
  | cons b rest ih =>
    have stepOne := one H (prefix_bit_step H second b rest (scanTapes rest header [] []) (emptyStk H))
    cases b with
    | true =>
      simpa [takeHeader, scanTapes, List.reverse_cons, List.append_assoc, Nat.add_comm,
        Nat.add_left_comm] using seq H stepOne (ih (true :: header) second)
    | false =>
      cases second with
      | false =>
        simpa [takeHeader, scanTapes, List.reverse_cons, List.append_assoc, Nat.add_comm,
          Nat.add_left_comm] using seq H stepOne (ih (false :: header) true)
      | true =>
        exact relax H stepOne (by simp)

private def batchEval (M : Bits → Bits) (w : Bits) : Bits :=
  let hdr := takeHeader w false
  match hdr.2 with
  | none => []
  | some xs => encodeWords ((decodeWordsAux xs []).map (fun x => M (hdr.1 ++ x)))

private def batchTime : Polynomial ℕ :=
  ((Polynomial.X : Polynomial ℕ) + 1) *
    (Polynomial.C 9 + Polynomial.C 5 * Polynomial.X +
      Polynomial.C (1 + 3 * Turing.TM2Comp.maxPushCount₁ H) * H.time)

private theorem batchTime_eval (L : ℕ) :
    (batchTime H).eval L = (L + 1) * (scanBudget H L + 3) := by
  simp [batchTime, scanBudget, outputBound]
  ring

private def batchRun (w : Bits) :
    Run H (atLabel H (.readHeader false) (scanTapes w [] [] []) (emptyStk H))
      (finalCfg H (batchEval M w)) ((batchTime H).eval w.length) := by
  rw [batchTime_eval]
  have hHead := headerRun H w [] false
  have hSize := takeHeader_length w false
  cases he : takeHeader w false with
  | mk header payload =>
    rw [he] at hHead hSize
    cases payload with
    | none =>
      have hLarge := scanBudget_ge H w.length
      have hStart : Run H (atLabel H (.readHeader false) (scanTapes w [] [] []) (emptyStk H))
          (atLabel H .clearWord (scanTapes [] header.reverse [] []) (emptyStk H)) (w.length + 1) := by
        simpa [headerResult] using hHead
      have hc := cleanup H header.reverse [] []
      have hRun := seq H hStart hc
      have hScale : scanBudget H w.length ≤ (w.length + 1) * scanBudget H w.length :=
        Nat.le_mul_of_pos_left _ (by omega)
      simp only [Option.map_none, Option.getD_none, Nat.add_zero] at hSize
      have hCost : (w.length + 1) + (([] : Bits).length + header.reverse.length +
          ([] : Bits).length + 3) ≤ (w.length + 1) * (scanBudget H w.length + 3) := by
        simp [List.length_reverse, hSize, Nat.mul_add]
        omega
      simpa [batchEval, he] using relax H hRun hCost
    | some input =>
      have hLen : header.reverse.length + ([] : Bits).length + input.length ≤ w.length := by
        simpa using hSize.le
      have hTail := scanRun H w.length input header.reverse [] [] hLen
      have hStart : Run H (atLabel H (.readHeader false) (scanTapes w [] [] []) (emptyStk H))
          (scanCfg H input header.reverse [] []) (w.length + 1) := by
        simpa [headerResult] using hHead
      have hScale : (input.length + 1) * scanBudget H w.length ≤
          (w.length + 1) * scanBudget H w.length :=
        Nat.mul_le_mul_right _ (by simp at hSize; omega)
      have hCost :
          (w.length + 1) +
          ((input.length + 1) * scanBudget H w.length + header.reverse.length +
            ([] : Bits).length + ([] : Bits).length) ≤
          (w.length + 1) * (scanBudget H w.length + 3) := by
        simp only [List.length_reverse, List.length_nil, Nat.add_zero, Nat.mul_add]
        simp at hSize
        omega
      simpa [batchEval, he] using relax H (seq H hStart hTail) hCost

private theorem cfg_eq {a b : Config H} (hl : a.l = b.l) (hv : a.var = b.var)
    (hs : ∀ k, a.stk k = b.stk k) : a = b := by
  have hstk := funext hs
  cases a
  cases b
  cases hl
  cases hv
  cases hstk
  rfl

private theorem initial (w : Bits) :
    initList (machine H) w =
      atLabel H (.readHeader false) (scanTapes w [] [] []) (emptyStk H) := by
  refine cfg_eq H (a := initList (machine H) w)
    (b := atLabel H (.readHeader false) (scanTapes w [] [] []) (emptyStk H)) rfl rfl ?_
  intro k
  cases k with
  | inl k => simp [initList, machine, config, TM2Call.stackUnion, emptyStk]
  | inr k => cases k <;> simp [initList, machine, config, TM2Call.stackUnion, scanTapes, Tapes.stk]

private theorem terminal (w : Bits) : haltList (machine H) w = finalCfg H w := by
  refine cfg_eq H (a := haltList (machine H) w) (b := finalCfg H w) rfl rfl ?_
  intro k
  cases k with
  | inl k => simp [haltList, machine, finalCfg, config, TM2Call.stackUnion, emptyStk]
  | inr k => cases k <;> simp [haltList, machine, finalCfg, config, TM2Call.stackUnion, Tapes.stk]

private def certificate : Witness (batchEval M) where
  tm := machine H
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := batchTime H
  outputsFun w := by
    change Run H (initList (machine H) (w.map id))
      (haltList (machine H) ((batchEval M w).map id)) ((batchTime H).eval w.length)
    simpa only [List.map_id, initial, terminal] using batchRun H w

private theorem takeHeader_replicate (n : ℕ) (w : Bits) (second : Bool) :
    takeHeader (List.replicate n true ++ w) second =
      (List.replicate n true ++ (takeHeader w second).1, (takeHeader w second).2) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, takeHeader, ih]

private theorem takeHeader_encAdvice (n a : ℕ) (w : Bits) :
    takeHeader (encAdvice n a w) false = (encAdvice n a [], some w) := by
  simp [encAdvice, enc, takeHeader_replicate, takeHeader]

private theorem decode_quote_append (w acc suffix : Bits) :
    decodeWordsAux (quoteBits w ++ false :: suffix) acc =
      (acc.reverse ++ w) :: decodeWordsAux suffix [] := by
  induction w generalizing acc with
  | nil => simp [quoteBits, decodeWordsAux]
  | cons b rest ih =>
    change decodeWordsAux (quoteBits rest ++ false :: suffix) (b :: acc) = _
    rw [ih]
    simp [List.reverse_cons, List.append_assoc]

private theorem decode_encode (words : List Bits) :
    decodeWordsAux (encodeWords words) [] = words := by
  induction words with
  | nil => rfl
  | cons w rest ih =>
    simp only [encodeWords, List.flatMap_cons, List.append_assoc, List.singleton_append]
    rw [decode_quote_append]
    simpa [encodeWords] using ih

/-- Run an arbitrary certified evaluator on each escaped word with the same
security parameter and advice, preserving word boundaries in the output. -/
theorem batchCalls : BatchCallsContract := by
  intro M hM
  obtain ⟨H⟩ := hM
  refine ⟨batchEval M, ⟨certificate H⟩, ?_⟩
  intro n a words
  unfold batchEval
  rw [takeHeader_encAdvice]
  simp only [decode_encode]
  simp [encAdvice, enc, List.append_assoc]

end

end HILL.PRG.BatchMachine

end HILL416_BatchMachine

section HILL416_RepeatSampler

namespace HILL.PRG

open MachineContracts HybridContracts

/-- Group the flat seed into words, run the certified sampler separately on each
word, and concatenate the outputs. -/
theorem repeatSampler : RepeatSamplerContract := by
  intro T k hT hk M hM
  obtain ⟨run, hRun, hEq⟩ := WordCodecs.plainBatchCalls_of_batchCalls BatchMachine.batchCalls M hM
  refine ⟨run ∘ BlockFormatter.format ∘ prepareRepeatInput T k,
    polytime_comp (polytime_comp (prepareRepeatInput_polytime hT hk) BlockFormatter.format_polytime) hRun,
    ?_⟩
  intro n a words hCount hLen
  simp only [Function.comp_apply, prepareRepeatInput_encAdvice, ← hCount]
  rw [BlockFormatter.format_encAdvice _ _ _ _ hLen, hEq]

/-- Independent repetition of a sampler is uniformly polynomial time in the HILL model. -/
theorem repeatPTime : RepeatPTimeContract := by
  intro F a k hF hk
  obtain ⟨hT, hL, hA, M, hM, hEval⟩ := hF
  obtain ⟨R, hR, hAgree⟩ := repeatSampler F.t k hT hk M hM
  refine ⟨(parameterArithmetic k F.t hk hT).2, (parameterArithmetic k F.ℓ hk hL).2, hA,
    R, hR, ?_⟩
  intro n seed hSeed
  have hSize : seed.length = k n * F.t n := mem_cube_iff_length.mp hSeed
  let xs := Blocks.block (k := k n) (F.t n) seed
  let words := List.ofFn xs
  have hLens (i : Fin (k n)) : (xs i).length = F.t n := Blocks.block_length hSize i
  have hCount : words.length = k n := List.length_ofFn
  have hWords : ∀ x ∈ words, x.length = F.t n := by
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact hLens i
  have hFlat : words.flatten = seed := Blocks.flatten_block hSize
  have hr : R (encAdvice n (a n) seed) =
      (words.map fun x => M (encAdvice n (a n) x)).flatten := by
    rw [← hFlat]
    exact hAgree n (a n) words hCount hWords
  refine ⟨?_, repeatEval_length F a k n (fun x hx => (hEval n x hx).2) seed hSeed⟩
  change R (encAdvice n (a n) seed) = repeatEval F k (a n) n seed
  rw [hr, ← Blocks.flatten_block (k := k n) (T := F.t n) hSize,
    repeatEval_flatten F a k n xs hLens]
  change (words.map fun x => M (encAdvice n (a n) x)).flatten =
    (List.ofFn fun i => F.f (a n) n (xs i)).flatten
  unfold words
  rw [List.map_ofFn]
  congr 2
  funext i
  exact (hEval n _ (mem_cube_iff_length.mpr (hLens i))).1

end HILL.PRG

end HILL416_RepeatSampler

section HILL416_HybridFinite

namespace HILL.PRG

open HybridContracts
open scoped BigOperators

private theorem repeat_law_pi {α β : Type*} [DecidableEq β]
    (S : Finset α) (f : α → β) (k : ℕ) (ys : Fin k → β) :
    lawOn (Fintype.piFinset (fun _ : Fin k => S)) (Proposed.repeatEval f) ys =
      ∏ i : Fin k, lawOn S f (ys i) := by
  change (Proposed.fiberCardOn (Fintype.piFinset (fun _ : Fin k => S))
      (fun xs i => f (xs i)) ys : ℝ) / _ = _
  rw [Proposed.productFiber, Fintype.card_piFinset, Nat.cast_prod, Nat.cast_prod]
  exact (Finset.prod_div_distrib _ _).symm

theorem repeatLawProduct : RepeatLawProductContract := by
  intro F a k hF n z
  obtain ⟨_, _, _, M, _, hM⟩ := hF
  let S := Fintype.piFinset (fun _ : Fin (k n) => cube (F.t n))
  let f := Proposed.repeatEval (F.f (a n) n) (k := k n)
  let Y := Fintype.piFinset (fun _ : Fin (k n) => cube (F.ℓ n))
  have hY (x : Fin (k n) → Bits) (hx : x ∈ S) : f x ∈ Y := by
    exact Fintype.mem_piFinset.mpr (fun i =>
      mem_cube_iff_length.mpr (hM n (x i) (Fintype.mem_piFinset.mp hx i)).2)
  have hSeed : Set.BijOn (Blocks.flatten (k := k n)) ↑S ↑(cube (k n * F.t n)) :=
    Blocks.flatten_bijOn (k n) (F.t n)
  have hOut : Set.BijOn (Blocks.flatten (k := k n)) ↑Y ↑(cube (k n * F.ℓ n)) :=
    Blocks.flatten_bijOn (k n) (F.ℓ n)
  have hLaw : repeatLaw F a k n = lawOn S (Blocks.flatten ∘ f) := by
    unfold repeatLaw
    rw [← lawOn_eq_of_bijOn hSeed (repeatEval F k (a n) n)]
    apply lawOn_congr
    intro x hx
    exact repeatEval_flatten F a k n x (fun i =>
      mem_cube_iff_length.mp (Fintype.mem_piFinset.mp hx i))
  rw [hLaw]
  unfold blockProductLaw
  split_ifs with hz
  · let ys := Blocks.block (k := k n) (F.ℓ n) z
    have hy : ys ∈ Y := Fintype.mem_piFinset.mpr
      (fun i => mem_cube_iff_length.mpr (Blocks.block_length hz i))
    have hyz : Blocks.flatten ys = z := Blocks.flatten_block hz
    have hfilt : S.filter (fun x => (Blocks.flatten ∘ f) x = z) =
        S.filter (fun x => f x = ys) := by
      ext x
      simp only [Finset.mem_filter, Function.comp_apply]
      exact and_congr_right (fun hx => hyz ▸ hOut.injOn.eq_iff (hY x hx) hy)
    have hWeights : lawOn S (Blocks.flatten ∘ f) z = lawOn S f ys := by
      unfold lawOn
      rw [hfilt]
    rw [hWeights, repeat_law_pi]
    exact Fin.prod_univ_eq_prod_range (fun i => F.law a n ((z.drop (i * F.ℓ n)).take (F.ℓ n))) _
  · unfold lawOn
    have hfilt : S.filter (fun x => (Blocks.flatten ∘ f) x = z) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro x hx he
      apply hz
      rw [← he]
      exact mem_cube_iff_length.mp (hOut.mapsTo (hY x hx))
    rw [hfilt]
    simp

private theorem lawOn_isProbOn {α β : Type*} [DecidableEq β]
    (S : Finset α) (Y : Finset β) (f : α → β) (hS : S.Nonempty)
    (hY : ∀ x ∈ S, f x ∈ Y) : IsProbOn Y (lawOn S f) := by
  constructor
  · intro y _
    unfold lawOn
    positivity
  · have himg : S.image f ⊆ Y := Finset.image_subset_iff.mpr hY
    have hZero (y : β) (_ : y ∈ Y) (hy : y ∉ S.image f) : lawOn S f y = 0 := by
      have ht : S.filter (fun x => f x = y) = ∅ :=
        Finset.filter_eq_empty_iff.mpr (fun x hx he => hy (Finset.mem_image.mpr ⟨x, hx, he⟩))
      simp [lawOn, ht]
    rw [← Finset.sum_subset himg hZero]
    simp only [lawOn, ← Finset.sum_div, ← Nat.cast_sum, ← Finset.card_eq_sum_card_image,
      div_self (Nat.cast_ne_zero.mpr hS.card_ne_zero : (S.card : ℝ) ≠ 0)]

theorem repeatLawProbOn : RepeatLawProbOnContract := by
  intro F a k hF n
  obtain ⟨_, _, _, M, _, hM⟩ := hF
  apply lawOn_isProbOn _ _ _ (Proposed.cube_nonempty _)
  exact fun x hx => mem_cube_iff_length.mpr
    (repeatEval_length F a k n (fun y hy => (hM n y hy).2) x hx)

theorem hybridStepSelection : HybridStepSelectionContract := by
  intro p k hk
  let d := fun i : ℕ => |p (i+1) - p i|
  obtain ⟨i, hi, hd⟩ := Finset.exists_max_image (Finset.range k) d (Finset.nonempty_range_iff.mpr hk.ne')
  refine ⟨i, Finset.mem_range.mp hi, ?_⟩
  calc
    _ = |∑ j ∈ Finset.range k, (p (j+1) - p j)| := congrArg abs (Finset.sum_range_sub p k).symm
    _ ≤ ∑ j ∈ Finset.range k, d j := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ ∈ Finset.range k, d i := Finset.sum_le_sum hd
    _ = _ := by simp [d]

theorem ptimeParamIsPoly : PTimeParamIsPolyContract := by
  intro k hk
  obtain ⟨c, _, hc⟩ := hk.1
  let d := max (k 0) c
  refine ⟨d, fun n => ?_⟩
  by_cases hn : n = 0
  · rw [hn]
    exact (le_max_left _ _).trans (Nat.le_add_left _ _)
  · have hn' : 1 ≤ n := Nat.pos_of_ne_zero hn
    have hu : k n ≤ c*n^c := by
      apply Nat.cast_le (α := ℝ) |>.mp
      simpa only [Nat.cast_mul, Nat.cast_pow] using (hc n hn').2
    exact hu.trans ((Nat.mul_le_mul (le_max_right _ _) (Nat.pow_le_pow_right hn'
      (le_max_right _ _))).trans (Nat.le_add_right _ _))

theorem negligibleNatMul : NegligibleNatMulContract := by
  intro q u hq hu j
  obtain ⟨c, hc⟩ := hq
  obtain ⟨N, hN⟩ := hu (j+c+1)
  refine ⟨max N (2*c+1), ?_⟩
  intro n hn
  have hN' : N ≤ n := (le_max_left _ _).trans hn
  have hn' : 2*c+1 ≤ n := (le_max_right _ _).trans hn
  have hnR : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr (by omega : 1 ≤ n)
  have hp : 0 < (n : ℝ) ^ j := pow_pos (by linarith) _
  have hqpow : (q n : ℝ) ≤ (n : ℝ) ^ (c+1) := by
    calc
      _ ≤ (c : ℝ) * (n : ℝ)^c + c := by exact_mod_cast hc n
      _ ≤ (c : ℝ) * (n : ℝ)^c + (c : ℝ) * (n : ℝ)^c :=
        add_le_add_right (le_mul_of_one_le_right (by positivity) (one_le_pow₀ hnR)) _
      _ = (2 * (c : ℝ)) * (n : ℝ)^c := by ring
      _ ≤ (n : ℝ) * (n : ℝ)^c :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast (show 2*c ≤ n by omega)) (by positivity)
      _ = _ := by rw [pow_succ, mul_comm]
  change (q n : ℝ) * u n < 1 / (n : ℝ)^j
  by_cases h0 : q n = 0
  · rw [h0, Nat.cast_zero, zero_mul]
    exact one_div_pos.mpr hp
  have hlt := mul_lt_mul_of_pos_left (hN n hN') (Nat.cast_pos.mpr (Nat.pos_of_ne_zero h0) : (0:ℝ) < q n)
  refine hlt.trans_le ((mul_le_mul_of_nonneg_right hqpow (by positivity)).trans_eq ?_)
  have hDen : (n : ℝ)^(j+c+1) = (n : ℝ)^j * (n : ℝ)^(c+1) := by
    exact (congrArg (fun i : ℕ => (n : ℝ)^i) (by omega : j+c+1 = j+(c+1))).trans (pow_add _ _ _)
  rw [hDen, mul_one_div]
  simpa only [one_mul] using
    mul_div_mul_right (1 : ℝ) ((n : ℝ)^j) (show (n : ℝ)^(c+1) ≠ 0 by positivity)

/-- Once a single uniform hybrid simulator is certified, the finite bound
implies the required asymptotic product indistinguishability. -/
theorem productCompIndist_of_simulator (hHybrid : ProductHybridContract) : ProductCompIndistContract :=
  InterfaceConsequences.productCompIndist_of_hybrid hHybrid negligibleNatMul ptimeParamIsPoly

end HILL.PRG

end HILL416_HybridFinite

section HILL416_AdviceBounds

namespace HILL.PRG

open ConstructionContracts

theorem isPoly_of_le {f g : ℕ → ℕ} (h : ∀ n, f n ≤ g n) (hg : IsPoly g) : IsPoly f := by
  obtain ⟨c, hc⟩ := hg
  exact ⟨c, fun n => (h n).trans (hc n)⟩

/-- A fixed pair of bounded integers still fits in polynomially many unary symbols. -/
theorem isPoly_pair {p q : ℕ → ℕ} (hp : IsPoly p) (hq : IsPoly q) :
    IsPoly (fun n => Nat.pair (p n) (q n)) := by
  obtain ⟨u, hu⟩ := hp
  obtain ⟨v, hv⟩ := hq
  let d := max u v
  let a := (2*d+1)^2
  let e := max (max (2*d) a) (Nat.pair (p 0) (q 0))
  refine ⟨e, ?_⟩
  intro n
  by_cases hn : n = 0
  · rw [hn]
    exact (le_max_right _ _).trans (Nat.le_add_left _ _)
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn
  have hUD : u ≤ d := le_max_left _ _
  have hVD : v ≤ d := le_max_right _ _
  have hpD : p n ≤ d*n^d+d :=
    (hu n).trans (Nat.add_le_add (Nat.mul_le_mul hUD (Nat.pow_le_pow_right hn0 hUD)) hUD)
  have hqD : q n ≤ d*n^d+d :=
    (hv n).trans (Nat.add_le_add (Nat.mul_le_mul hVD (Nat.pow_le_pow_right hn0 hVD)) hVD)
  have hmax : max (p n) (q n) + 1 ≤ (2*d+1)*n^d := by
    calc
      _ ≤ (d*n^d+d) + 1 := Nat.add_le_add_right (max_le hpD hqD) 1
      _ ≤ d*n^d + (d+1)*n^d := by
        rw [Nat.add_assoc]
        exact Nat.add_le_add_left (Nat.le_mul_of_pos_right _ (Nat.pow_pos hn0)) _
      _ = _ := by ring
  have ha : a ≤ e := (le_max_right _ _).trans (le_max_left _ _)
  have he' : 2*d ≤ e := (le_max_left (2*d) a).trans (le_max_left _ _)
  have he : d*2 ≤ e := by simpa only [Nat.mul_comm d 2] using he'
  calc
    _ ≤ (max (p n) (q n) + 1)^2 := (Nat.pair_lt_max_add_one_sq _ _).le
    _ ≤ ((2*d+1)*n^d)^2 := Nat.pow_le_pow_left hmax _
    _ = a * n^(d*2) := by rw [mul_pow, ← pow_mul]
    _ ≤ e*n^e := Nat.mul_le_mul ha (Nat.pow_le_pow_right hn0 he)
    _ ≤ _ := Nat.le_add_right _ _

theorem packAdvice_isPoly {a j N : ℕ → ℕ} (ha : IsPoly a) (hN : PTimeParam N)
    (hj : ∀ n, j n ≤ N n) : IsPoly (packAdvice a j) :=
  isPoly_pair ha (isPoly_of_le hj (ptimeParamIsPoly N hN))

/-- The two decoded lengths fit in the tape whose size encodes them. -/
theorem decoded_lengths_le (total : ℕ) :
    (Nat.unpair total).1 + (Nat.unpair total).2 ≤ total :=
  Nat.unpair_add_le total

/-- Scan one unary token at a time. The state is the square index and its remainder. -/
def squareWalk : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | m + 1 =>
    let (t, r) := squareWalk m
    if r = 2 * t then (t + 1, 0) else (t, r + 1)

theorem squareWalk_spec (m : ℕ) :
    (squareWalk m).1 * (squareWalk m).1 + (squareWalk m).2 = m ∧
      (squareWalk m).2 ≤ 2 * (squareWalk m).1 := by
  induction m with
  | zero => decide
  | succ m ih =>
    cases h : squareWalk m with
    | mk t r =>
      rw [h] at ih
      simp only [squareWalk, h]
      split_ifs with hR
      · obtain ⟨hEq, _⟩ := ih
        simp only [Prod.fst, Prod.snd, hR] at hEq
        constructor
        · simp only [Nat.add_zero]
          nlinarith
        · omega
      · obtain ⟨hEq, hLe⟩ := ih
        simp only [Prod.fst, Prod.snd] at hEq hLe ⊢
        exact ⟨by omega, by omega⟩

/-- Decode the square enumeration used by Mathlib's pairing function. -/
def unpairBySquareWalk (m : ℕ) : ℕ × ℕ :=
  let (t, r) := squareWalk m
  if r < t then (r, t) else (t, r - t)

theorem unpairBySquareWalk_eq (m : ℕ) : unpairBySquareWalk m = Nat.unpair m := by
  have hSpec := squareWalk_spec m
  cases h : squareWalk m with
  | mk t r =>
    rw [h] at hSpec
    obtain ⟨hEq, hLe⟩ := hSpec
    simp only [Prod.fst, Prod.snd] at hEq hLe
    have hCode : Nat.pair (unpairBySquareWalk m).1 (unpairBySquareWalk m).2 = m := by
      simp only [unpairBySquareWalk, h]
      split_ifs with hR
      · simpa only [Nat.pair, Prod.fst, Prod.snd, if_pos hR] using hEq
      · have hSub : ¬ t < r - t := by omega
        simp only [Nat.pair, Prod.fst, Prod.snd, if_neg hSub]
        omega
    calc
      _ = Nat.unpair (Nat.pair (unpairBySquareWalk m).1 (unpairBySquareWalk m).2) := by simp
      _ = Nat.unpair m := congrArg Nat.unpair hCode

end HILL.PRG

end HILL416_AdviceBounds

section HILL416_SamplerMachines

set_option backward.isDefEq.respectTransparency.types false

namespace HILL.PRG

open WordCodecs ConstructionContracts HybridContracts MachineContracts
open CLRS.Chapter34.Turing.PolyBuilder

theorem keyWidthPTime {N : ℕ → ℕ} (hN : PTimeParam N) :
    PTimeParam (fun n => keyWidth (N n)) :=
  (parameterArithmetic N (fun n => N n + 1) hN
    (parameterArithmetic N (fun _ => 1) hN onePTimeParam).1).2

private def zerosSpec : StatefulFlatMapSpec Unit Bool Bool where
  initial := ()
  action _ _ := ([false], ())
  finish _ := []

private theorem zerosSpec_apply (w : Bits) :
    rewriteStatefulFlatMap zerosSpec w = List.replicate w.length false := by
  induction w with
  | nil => rfl
  | cons b w ih => exact congrArg (false :: ·) ih

private theorem zeros_polytime :
    PolyTimeComputable (fun w : Bits => List.replicate w.length false) :=
  (funext zerosSpec_apply) ▸ ⟨statefulFlatMap_computableInPolyTime zerosSpec⟩

/-- Pad the output of a certified prefix evaluator to a length computed from n. -/
theorem padToWidth (N : ℕ → ℕ) (hN : PTimeParam N)
    (Q : Bits → Bits) (hQ : PolyTimeComputable Q) :
    ∃ P : Bits → Bits, PolyTimeComputable P ∧
      ∀ n a w, let z := Q (encAdvice n a w)
        z.length ≤ N n →
        P (encAdvice n a w) = z ++ List.replicate (N n - z.length) false := by
  obtain ⟨T, hT, hTake⟩ := payloadTake N hN
  let zeros (w : Bits) := List.replicate (N (unaryParameter w).length) false
  have hz : PolyTimeComputable zeros := by
    have h := polytime_comp (polytime_comp unaryParameter_polytime hN.2) zeros_polytime
    simpa only [zeros, Function.comp_def, List.length_replicate] using h
  let input (w : Bits) := splitAdviceHeader true w ++ (Q w ++ zeros w)
  refine ⟨T ∘ input, polytime_comp
    (polytime_append (splitAdviceHeader_polytime true) (polytime_append hQ hz)) hT, ?_⟩
  intro n a w z h
  have hin : input (encAdvice n a w) = encAdvice n a (z ++ List.replicate (N n) false) := by
    simp only [input, splitAdviceHeader_encAdvice, if_true, zeros, unaryParameter_encAdvice,
      List.length_replicate, z]
    simp [encAdvice, enc, List.append_assoc]
  have hl : N n ≤ (z ++ List.replicate (N n) false).length := by
    simp
  rw [Function.comp_apply, hin, hTake _ _ _ hl, List.take_append,
    List.take_of_length_le h, List.take_replicate, Nat.min_eq_left (Nat.sub_le _ _)]

set_option maxHeartbeats 1200000 in
/-- The ideal sampler is polynomial time at the packed advice used by the construction. -/
theorem idealGeneratorPTime : IdealGeneratorPTimeContract := by
  intro F a k N j hF hk hN hj
  obtain ⟨hSeed, hLen, hAdv, R, hR, hEval⟩ := repeatPTime F a k hF hk
  let t := seedWidth F k
  let p := fun n => keyWidth (N n)
  have hp : PTimeParam p := keyWidthPTime hN
  have ht : PTimeParam t := hSeed
  have htN : PTimeParam (fun n => t n + N n) := (parameterArithmetic t N ht hN).1
  have htNP := (parameterArithmetic (fun n => t n + N n) p htN hp).1
  have hlN := (parameterArithmetic (fun n => k n * F.ℓ n) N hLen hN).1
  have hlNP := (parameterArithmetic (fun n => k n * F.ℓ n + N n) p hlN hp).1
  obtain ⟨X, hX, hx⟩ := payloadTake t ht
  obtain ⟨Z, hZ, hz⟩ := payloadSlice t N ht hN
  obtain ⟨K, hK, hkey⟩ := payloadSlice (fun n => t n + N n) p htN hp
  let Q := takeUnary ∘ (fun w => adviceSecondField w ++ Z w)
  have hQ : PolyTimeComputable Q :=
    polytime_comp (f := fun w => adviceSecondField w ++ Z w) (g := takeUnary)
      (polytime_append (f := adviceSecondField) (g := Z) adviceSecondField_polytime hZ)
      takeUnary_polytime
  obtain ⟨P, hP, hPad⟩ := padToWidth N hN Q hQ
  let run (w : Bits) := (R ∘ unpackFirstInput X) w ++ (P w ++ K w)
  have hRun : PolyTimeComputable run :=
    polytime_append (f := R ∘ unpackFirstInput X) (g := fun w => P w ++ K w)
      (polytime_comp (f := unpackFirstInput X) (g := R) (unpackFirstInput_polytime hX) hR)
      (polytime_append (f := P) (g := K) hP hK)
  refine ⟨htNP, hlNP, packAdvice_isPoly hAdv hN hj, run, hRun, ?_⟩
  intro n w hw
  have hsize : w.length = t n + N n + p n := mem_cube_iff_length.mp hw
  have hXsize : t n ≤ w.length := by omega
  have hZsize : t n + N n ≤ w.length := by omega
  let x := w.take (t n)
  let z := (w.drop (t n)).take (N n)
  let r := (w.drop (t n + N n)).take (p n)
  have hxl : x.length = t n := by simp only [x, List.length_take, Nat.min_eq_left hXsize]
  have hxc : x ∈ cube ((repeatEns F k).t n) := mem_cube_iff_length.mpr hxl
  have hzl : z.length = N n := by
    simp only [z, List.length_take, List.length_drop]
    omega
  have hrl : r.length = p n := by
    simp only [r, List.length_take, List.length_drop]
    omega
  let input := encAdvice n (packAdvice a j n) w
  have hx' : X input = x := hx n _ w hXsize
  have hz' : Z input = z := hz n _ w hZsize
  have hr' : K input = r := hkey n _ w hsize.ge
  have hJfield : adviceSecondField input = List.replicate (j n) true ++ [false] :=
    adviceSecondField_encAdvice n (a n) (j n) w
  have hjz : j n ≤ z.length := hzl ▸ hj n
  have hQ' : Q input = z.take (j n) := by
    simp only [Q, Function.comp_apply, hJfield, hz', List.append_assoc,
      List.singleton_append, takeUnary_replicate _ _ hjz]
  have hQl : (Q input).length = j n := by simp [hQ', hzl, Nat.min_eq_left (hj n)]
  have hP' : P input = padPrefix (N n) (j n) z := by
    have hle : (Q input).length ≤ N n := hQl ▸ hj n
    rw [hPad n _ w hle, hQ', List.length_take, hzl, Nat.min_eq_left (hj n), padPrefix]
  have hR' := hEval n x hxc
  have hUnpack : unpackFirstInput X input = encAdvice n (a n) x := by
    change unpackFirstInput X (encAdvice n (Nat.pair (a n) (j n)) w) = _
    rw [unpackFirstInput_encAdvice, show X (encAdvice n (Nat.pair (a n) (j n)) w) = x from hx']
  have hout : (idealGenerator F k N).f (packAdvice a j n) n w =
      repeatEval F k (a n) n x ++ (padPrefix (N n) (j n) z ++ r) := by
    simp only [idealGenerator, packAdvice, Nat.unpair_pair, Nat.min_eq_left (hj n),
      x, z, r, t, p, seedWidth, List.append_assoc]
  constructor
  · change run input = _
    rw [hout]
    simp only [run, Function.comp_apply, hUnpack, hP', hr', hR'.1, repeatEns]
  · rw [hout]
    have hRep : (repeatEval F k (a n) n x).length = k n * F.ℓ n := hR'.2
    simp only [List.length_append, hRep, padPrefix, List.length_take, hzl,
      Nat.min_eq_left (hj n), List.length_replicate, hrl, idealGenerator, p]
    omega

set_option maxHeartbeats 1200000 in
/-- An affine evaluator suffices to certify the complete padded hash generator. -/
theorem hashGeneratorPTime_of_affine (hAffine : AffineEvaluatorContract) :
    HashGeneratorPTimeContract := by
  intro F a k j hF hk hj
  obtain ⟨A, hA, hAffineEval⟩ := hAffine
  obtain ⟨hSeed, hLen, hAdv, R, hR, hEval⟩ := repeatPTime F a k hF hk
  let N := seedWidth F k
  let p := fun n => keyWidth (N n)
  have hN : PTimeParam N := hSeed
  have hp : PTimeParam p := keyWidthPTime hN
  have ht := (parameterArithmetic N p hN hp).1
  have hlN := (parameterArithmetic (fun n => k n * F.ℓ n) N hLen hN).1
  have hl := (parameterArithmetic (fun n => k n * F.ℓ n + N n) p hlN hp).1
  obtain ⟨X, hX, hx⟩ := payloadTake N hN
  obtain ⟨K, hK, hkey⟩ := payloadSlice N p hN hp
  let affineInput (w : Bits) :=
    unaryField N w ++ (adviceSecondField w ++ (K w ++ X w))
  have hInput : PolyTimeComputable affineInput :=
    polytime_append (unaryField_polytime hN)
      (polytime_append adviceSecondField_polytime (polytime_append hK hX))
  let Q := A ∘ affineInput
  obtain ⟨P, hP, hPad⟩ := padToWidth N hN Q (polytime_comp hInput hA)
  let run (w : Bits) := (R ∘ unpackFirstInput X) w ++ (P w ++ K w)
  have hRun : PolyTimeComputable run :=
    polytime_append (f := R ∘ unpackFirstInput X) (g := fun w => P w ++ K w)
      (polytime_comp (f := unpackFirstInput X) (g := R) (unpackFirstInput_polytime hX) hR)
      (polytime_append (f := P) (g := K) hP hK)
  refine ⟨ht, hl, packAdvice_isPoly hAdv hN hj, run, hRun, ?_⟩
  intro n w hw
  have hsize : w.length = N n + p n := mem_cube_iff_length.mp hw
  have hXsize : N n ≤ w.length := by omega
  let x := w.take (N n)
  let r := (w.drop (N n)).take (p n)
  have hxl : x.length = N n := by
    simp [x, Nat.min_eq_left hXsize]
  have hrl : r.length = p n := by
    simp [r, hsize]
  have hxC : x ∈ cube (N n) := mem_cube_iff_length.mpr hxl
  have hrC : r ∈ cube (p n) := mem_cube_iff_length.mpr hrl
  let input := encAdvice n (packAdvice a j n) w
  have hx' : X input = x := hx n _ w hXsize
  have hr' : K input = r := hkey n _ w hsize.ge
  have hAIn : affineInput input = encAdvice (N n) (j n) (r ++ x) := by
    simp only [affineInput, input, packAdvice, unaryField_encAdvice, adviceSecondField_encAdvice,
      show X (encAdvice n (Nat.pair (a n) (j n)) w) = x from hx',
      show K (encAdvice n (Nat.pair (a n) (j n)) w) = r from hr']
    simp [encAdvice, enc, List.append_assoc]
  have hQ' : Q input = affinePrefix (N n) (j n) r x := by
    rw [show Q input = A (affineInput input) from rfl, hAIn]
    exact hAffineEval _ _ (hj n) r hrC x hxC
  have hQl : (Q input).length = j n := by simp [hQ', affinePrefix]
  have hP' : P input = paddedAffine (N n) (j n) r x := by
    have hle : (Q input).length ≤ N n := hQl ▸ hj n
    rw [hPad n _ w hle, hQl, hQ', paddedAffine, Nat.min_eq_left (hj n)]
  have hR' := hEval n x (show x ∈ cube ((repeatEns F k).t n) from hxC)
  have hUnpack : unpackFirstInput X input = encAdvice n (a n) x := by
    change unpackFirstInput X (encAdvice n (Nat.pair (a n) (j n)) w) = _
    rw [unpackFirstInput_encAdvice, show X (encAdvice n (Nat.pair (a n) (j n)) w) = x from hx']
  have hout : (hashGenerator F k).f (packAdvice a j n) n w =
      repeatEval F k (a n) n x ++ (paddedAffine (N n) (j n) r x ++ r) := by
    simp only [hashGenerator, packAdvice, Nat.unpair_pair, List.append_assoc, x, r, N, p]
  constructor
  · change run input = _
    rw [hout]
    simp only [run, Function.comp_apply, hUnpack, hP', hr', hR'.1, repeatEns]
  · rw [hout]
    have hRep : (repeatEval F k (a n) n x).length = k n * F.ℓ n := hR'.2
    change (repeatEval F k (a n) n x ++ (paddedAffine (N n) (j n) r x ++ r)).length =
      k n * F.ℓ n + N n + p n
    simp only [List.length_append, hRep, paddedAffine,
      affinePrefix, List.length_map, List.length_range, List.length_replicate, hrl]
    omega

end HILL.PRG

end HILL416_SamplerMachines

section HILL416_Reduction

namespace HILL.PRG

open ConstructionContracts MachineContracts

private theorem polyParam_seed_add_one {T : ℕ → ℕ}
    (h : PolyParam (fun n => (T n : ℝ))) : PolyParam (fun n => (T n : ℝ) + 1) := by
  obtain ⟨c, hc, hp⟩ := h
  refine ⟨c + 1, by omega, ?_⟩
  intro n hn
  have hn' : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr hn
  have hpow := one_le_pow₀ (n := c) hn'
  have hC : 0 < ((c + 1 : ℕ) : ℝ) := by positivity
  have hb : 1 ≤ ((c + 1 : ℕ) : ℝ) * (n : ℝ) ^ (c + 1) :=
    one_le_mul_of_one_le_of_one_le (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) c])
      (one_le_pow₀ hn')
  constructor
  · exact (div_le_one_of_le₀ hb (zero_le_one.trans hb)).trans
      (by linarith [Nat.cast_nonneg (α := ℝ) (T n)])
  · calc
      _ ≤ (c : ℝ) * (n : ℝ) ^ c + 1 := add_le_add_left (hp n hn).2 _
      _ ≤ (c : ℝ) * (n : ℝ) ^ c + (n : ℝ) ^ c := add_le_add_right hpow _
      _ = ((c + 1 : ℕ) : ℝ) * (n : ℝ) ^ c := by push_cast; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hn' (by omega)) hC.le

/-- Assemble the exact HILL 4.16 reduction from the remaining construction properties. -/
theorem falseEntropyToPseudoentropy_of_construction
    (hGen : HashGeneratorPTimeContract)
    (hIdeal : IdealGeneratorPTimeContract)
    (hIndist : ConstructionCompIndistContract) :
    (∃ (F : FunEns) (a : ℕ → ℕ) (s : ℕ → ℝ), PolyParam s ∧ IsFalseEntropyGen F a s) →
      ∃ (G : FunEns) (b : ℕ → ℕ) (t : ℕ → ℝ), PolyParam t ∧ IsPseudoentropyGen G b t := by
  rintro ⟨F, a, s, hs, hF, _, W, hW, hEq, hCI, M, hM⟩
  obtain ⟨C, d, hC, hbound⟩ := repetitionSchedule_bounds hF.1.1 hs
  let k := repetitionSchedule C d
  let N := seedWidth F k
  let j := chosenWidth F a k s
  let b := packAdvice a j
  let G := hashGenerator F k
  let I := idealGenerator F k N
  let V := idealGenerator W k N
  have hk : PTimeParam k := schedulePTime C d hC
  have hN : PTimeParam N := (parameterArithmetic k F.t hk hF.1).2
  have hj (n : ℕ) (hn : 1 ≤ n) :
      j n = Nat.floor ((k n : ℝ) *
        ((F.t n : ℝ) - shannonOn (cube (F.ℓ n)) (F.law a n) - s n / 2)) := by
    simp [j, chosenWidth, show n ≠ 0 by omega]
  have hwidth (n : ℕ) : j n ≤ N n := by
    by_cases hn : 1 ≤ n
    · rw [hj n hn]
      exact hashWidthBound (F.t n) (k n) _ _ (shannonOn_lawOn_nonneg _ _ _)
        (hbound n hn).1.le
    · have hz : n = 0 := by omega
      simp [hz, j, chosenWidth]
  have hG : G.PTime b := hGen F a k j hF hk hwidth
  have hV : V.PTime b := hIdeal W a k N j hW hk hN hwidth
  have hLen (X : FunEns) (hX : X.PTime a) (n : ℕ) (x : Bits) (hx : x ∈ cube (X.t n)) :
      (X.f (a n) n x).length = X.ℓ n := by
    obtain ⟨_, _, _, f, _, hf⟩ := hX
    exact (hf n x hx).2
  have hSame : V.ℓ = G.ℓ := by
    simp [V, G, idealGenerator, hashGenerator, hEq, N]
  have hStat : Negligible (fun n => statDistOn (cube (G.ℓ n)) (G.law b n) (I.law b n)) := by
    apply InterfaceConsequences.negligibleMono (v := extractionError) _ ?_ extractionErrorNegligible
    refine ⟨1, fun n hn => ?_⟩
    obtain ⟨hsn, hmargin, hvar⟩ := hbound n hn
    exact constructionExtraction F a k j s n hn (fun x hx => hLen F hF n x hx) hsn (hj n hn) hmargin hvar
  have hComp : CompIndist b G.ℓ (G.law b) (V.law b) :=
    compIndist_trans (compIndist_of_negligible_statDist b G.ℓ _ _ hStat)
      (hIndist F W a k j hF hW hEq hk hwidth hCI)
  refine ⟨G, b, fun _ => 1,
    InterfaceConsequences.pseudoentropy_of_witness G V b hG hV hSame
      (polyParam_seed_add_one hG.1.1) hComp ⟨M, ?_⟩⟩
  intro n hn hn1
  rw [← hSame, idealGeneratorEntropy W a k N j (hLen W hW) hwidth n, hEq]
  have hbig : 4 ≤ (k n : ℝ) * s n := by
    have hmargin := (hbound n hn1).2.1
    dsimp only [k] at *
    linarith [Nat.cast_nonneg (α := ℝ) n]
  exact floorEntropyGain (F.t n) (k n) (j n) (keyWidth (N n))
    (shannonOn (cube (F.ℓ n)) (F.law a n))
    (shannonOn (cube (F.ℓ n)) (W.law a n)) (s n)
    (by simpa only [IsFalseEntropyGen, IsPseudoentropyGen] using hM n hn hn1)
    hbig (hj n hn1)

/-- The remaining premises are affine evaluation and indistinguishability of the ideal laws. -/
theorem falseEntropyToPseudoentropy_of_affine_and_indist
    (hAffine : AffineEvaluatorContract)
    (hIndist : ConstructionCompIndistContract) :
    (∃ (F : FunEns) (a : ℕ → ℕ) (s : ℕ → ℝ), PolyParam s ∧ IsFalseEntropyGen F a s) →
      ∃ (G : FunEns) (b : ℕ → ℕ) (t : ℕ → ℝ), PolyParam t ∧ IsPseudoentropyGen G b t :=
  falseEntropyToPseudoentropy_of_construction
    (hashGeneratorPTime_of_affine hAffine) idealGeneratorPTime hIndist

end HILL.PRG

end HILL416_Reduction

section HILL416_DropPrefix

set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSimpArgs false

namespace HILL.PRG.DropPrefix

open Turing StateTransition WordCodecs

noncomputable section

inductive Tape
  | input | width | outRev | output
  deriving DecidableEq, Fintype

inductive Label
  | readWidth | skip | copy | reverseOutput
  deriving DecidableEq, Fintype

private abbrev Γ : Tape → Type := fun _ => Bool
private abbrev Stmt := TM2.Stmt Γ Label (Option Bool)
private abbrev Cfg := TM2.Cfg Γ Label (Option Bool)

private def jump (l : Label) : Stmt := .load (fun _ => none) (.goto (fun _ => l))

private def push (t : Tape) (b : Bool) (next : Stmt) : Stmt := .push t (fun _ => b) next

private def pop (t : Tape) (empty : Stmt) (bit : Bool → Stmt) : Stmt :=
  .pop t (fun _ b => b)
    (.branch Option.isSome (.branch (fun b => b.getD false) (bit true) (bit false)) empty)

private def program : Label → Stmt
  | .readWidth => pop .input (jump .skip) (fun b =>
    if b then push .width true (jump .readWidth) else jump .skip)
  | .skip => pop .width (jump .copy) (fun _ => pop .input (jump .skip) (fun _ => jump .skip))
  | .copy => pop .input (jump .reverseOutput) (fun b => push .outRev b (jump .copy))
  | .reverseOutput =>
    pop .outRev (.load (fun _ => none) .halt) (fun b => push .output b (jump .reverseOutput))

private def stk (input width rev out : Bits) : Tape → Bits
  | .input => input
  | .width => width
  | .outRev => rev
  | .output => out

private def cfg (l : Label) (input width rev out : Bits) : Cfg :=
  ⟨some l, none, stk input width rev out⟩

private def done (out : Bits) : Cfg := ⟨none, none, stk [] [] [] out⟩

private def machine : FinTM2 where
  K := Tape
  k₀ := .input
  k₁ := .output
  Γ := Γ
  Λ := Label
  main := .readWidth
  σ := Option Bool
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := program

private abbrev step := TM2.step program
private abbrev Run (x y : Cfg) (n : ℕ) := EvalsToInTime step x (some y) n

private def one {x y : Cfg} (h : step x = some y) : Run x y 1 :=
  ⟨⟨1, h⟩, le_rfl⟩

private def seq {a b c : Cfg} {m n : ℕ} (x : Run a b m) (y : Run b c n) : Run a c (m+n) :=
  ⟨(EvalsToInTime.trans _ _ _ _ _ _ x y).toEvalsTo,
    (Nat.add_le_add y.steps_le_m x.steps_le_m).trans_eq (Nat.add_comm _ _)⟩

private def relax {a b : Cfg} {m n : ℕ} (h : Run a b m) (hle : m ≤ n) : Run a b n :=
  ⟨h.toEvalsTo, h.steps_le_m.trans hle⟩

private def fields : Bits → ℕ × Bits
  | [] => (0, [])
  | false :: xs => (0, xs)
  | true :: xs => ((fields xs).1 + 1, (fields xs).2)

private theorem fields_spec (n : ℕ) (w : Bits) :
    fields (List.replicate n true ++ false :: w) = (n, w) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, fields, ih]

private theorem fields_bound (w : Bits) : (fields w).1 + (fields w).2.length ≤ w.length := by
  induction w with
  | nil => rfl
  | cons b xs ih =>
    cases b with
    | false => simp [fields]
    | true => simp only [fields, List.length_cons]; omega

def run (w : Bits) : Bits := (fields w).2.drop (fields w).1

theorem run_replicate (n : ℕ) (w : Bits) :
    run (List.replicate n true ++ false :: w) = w.drop n := by
  simp only [run, fields_spec]

private theorem readTrue (xs a rev out : Bits) :
    step (cfg .readWidth (true :: xs) a rev out) = some (cfg .readWidth xs (true :: a) rev out) := by
  (simp [cfg, done, program, pop, push, jump, stk, Function.update] <;>
    (funext k; cases k <;> simp [stk, Function.update]))

private theorem readEnd (xs a rev out : Bits) :
    step (cfg .readWidth (false :: xs) a rev out) = some (cfg .skip xs a rev out) := by
  (simp [cfg, done, program, pop, push, jump, stk, Function.update] <;>
    (funext k; cases k <;> simp [stk, Function.update]))

private theorem readEmpty (a rev out : Bits) :
    step (cfg .readWidth [] a rev out) = some (cfg .skip [] a rev out) := by
  (simp [cfg, done, program, pop, push, jump, stk, Function.update] <;>
    (funext k; cases k <;> simp [stk, Function.update]))

private def readRun (w a rev out : Bits) :
    let p := fields w
    Run (cfg .readWidth w a rev out)
      (cfg .skip p.2 (List.replicate p.1 true ++ a) rev out) (p.1 + 1) := by
  induction w generalizing a with
  | nil => exact one (readEmpty a rev out)
  | cons b xs ih =>
    cases b with
    | false => exact one (readEnd xs a rev out)
    | true =>
      have hrepr (n : ℕ) : List.replicate n true ++ true :: a =
          List.replicate (n+1) true ++ a := by
        rw [List.replicate_add]
        simp [List.append_assoc]
      simpa only [fields, hrepr, Nat.add_comm 1 ((fields xs).1 + 1)] using
        seq (one (readTrue xs a rev out)) (ih (true :: a))

private theorem skipStep (w width rev out : Bits) :
    step (cfg .skip w (true :: width) rev out) = some (cfg .skip w.tail width rev out) := by
  cases w with
  | nil => (simp [cfg, done, program, pop, push, jump, stk, Function.update] <;>
    (funext k; cases k <;> simp [stk, Function.update]))
  | cons b xs => cases b <;> (simp [cfg, done, program, pop, push, jump, stk, Function.update] <;>
    (funext k; cases k <;> simp [stk, Function.update]))

private theorem skipEnd (w rev out : Bits) :
    step (cfg .skip w [] rev out) = some (cfg .copy w [] rev out) := by
  (simp [cfg, done, program, pop, push, jump, stk, Function.update] <;>
    (funext k; cases k <;> simp [stk, Function.update]))

private def skipRun (w : Bits) (n : ℕ) (rev out : Bits) :
    Run (cfg .skip w (List.replicate n true) rev out)
      (cfg .copy (w.drop n) [] rev out) (n + 1) := by
  induction n generalizing w with
  | zero => exact one (skipEnd w rev out)
  | succ n ih =>
    have hd : w.drop (n + 1) = w.tail.drop n := by cases w <;> simp
    simpa only [hd, List.replicate_succ, Nat.add_comm 1 (n + 1)] using
      seq (one (skipStep w (List.replicate n true) rev out)) (ih w.tail)

private theorem copyStep (b : Bool) (xs rev out : Bits) :
    step (cfg .copy (b :: xs) [] rev out) = some (cfg .copy xs [] (b :: rev) out) := by
  cases b <;> (simp [cfg, done, program, pop, push, jump, stk, Function.update] <;>
    (funext k; cases k <;> simp [stk, Function.update]))

private theorem copyEnd (rev out : Bits) :
    step (cfg .copy [] [] rev out) = some (cfg .reverseOutput [] [] rev out) := by
  (simp [cfg, done, program, pop, push, jump, stk, Function.update] <;>
    (funext k; cases k <;> simp [stk, Function.update]))

private def copyRun (w rev out : Bits) :
    Run (cfg .copy w [] rev out)
      (cfg .reverseOutput [] [] (w.reverse ++ rev) out) (w.length + 1) := by
  induction w generalizing rev with
  | nil => exact one (copyEnd rev out)
  | cons b xs ih =>
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append, List.length_cons,
      Nat.add_comm 1 (xs.length + 1)] using seq (one (copyStep b xs rev out)) (ih (b :: rev))

private theorem emitStep (b : Bool) (w out : Bits) :
    step (cfg .reverseOutput [] [] (b :: w) out) = some (cfg .reverseOutput [] [] w (b :: out)) := by
  cases b <;> (simp [cfg, done, program, pop, push, jump, stk, Function.update] <;>
    (funext k; cases k <;> simp [stk, Function.update]))

private theorem emitEnd (out : Bits) :
    step (cfg .reverseOutput [] [] [] out) = some (done out) := by
  (simp [cfg, done, program, pop, push, jump, stk, Function.update] <;>
    (funext k; cases k <;> simp [stk, Function.update]))

private def emitRun (rev out : Bits) :
    Run (cfg .reverseOutput [] [] rev out) (done (rev.reverse ++ out)) (rev.length + 1) := by
  induction rev generalizing out with
  | nil => exact one (emitEnd out)
  | cons b xs ih =>
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append, List.length_cons,
      Nat.add_comm 1 (xs.length + 1)] using seq (one (emitStep b xs out)) (ih (b :: out))

private def runTime (w : Bits) :
    Run (cfg .readWidth w [] [] []) (done (run w)) (2 * w.length + 4) := by
  let p := fields w
  let tail := p.2.drop p.1
  have hread : Run (cfg .readWidth w [] [] []) (cfg .skip p.2 (List.replicate p.1 true) [] []) (p.1 + 1) := by
    simpa only [List.append_nil] using readRun w [] [] []
  have hcopy : Run (cfg .copy tail [] [] [])
      (cfg .reverseOutput [] [] tail.reverse []) (tail.length + 1) := by
    simpa only [List.append_nil] using copyRun tail [] []
  have hemit : Run (cfg .reverseOutput [] [] tail.reverse []) (done tail) (tail.length + 1) := by
    simpa only [List.append_nil, List.reverse_reverse, List.length_reverse] using emitRun tail.reverse []
  have hb : p.1 + p.2.length ≤ w.length := fields_bound w
  have ht : tail.length ≤ p.2.length := by simp [tail]
  exact relax (seq (seq (seq hread (skipRun p.2 p.1 [] [])) hcopy) hemit) (by omega)

private theorem cfg_eq {c d : Cfg} (hl : c.l = d.l) (hv : c.var = d.var)
    (hs : ∀ t, c.stk t = d.stk t) : c = d := by
  have he := funext hs
  cases c
  cases d
  cases hl
  cases hv
  cases he
  rfl

private theorem init_eq (w : Bits) : initList machine w = cfg .readWidth w [] [] [] := by
  refine cfg_eq (c := initList machine w) (d := cfg .readWidth w [] [] []) rfl rfl ?_
  intro t
  cases t <;> simp [machine, initList, cfg, stk]

private theorem halt_eq (w : Bits) : haltList machine w = done w := by
  refine cfg_eq (c := haltList machine w) (d := done w) rfl rfl ?_
  intro t
  cases t <;> simp [machine, haltList, done, stk]

theorem run_polytime : PolyTimeComputable run := by
  let time : Polynomial ℕ := Polynomial.C 2 * Polynomial.X + Polynomial.C 4
  refine ⟨{
    tm := machine
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Equiv.refl Bool
    time := time
    outputsFun := ?_ }⟩
  intro w
  change Run (initList machine (w.map id)) (haltList machine ((run w).map id))
    (time.eval w.length)
  simpa only [List.map_id, init_eq, halt_eq, time, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X] using runTime w

end

end HILL.PRG.DropPrefix

end HILL416_DropPrefix

section HILL416_AdviceSimulation

set_option backward.isDefEq.respectTransparency.types false

namespace HILL.PRG

open WordCodecs HybridContracts

/-- Drop a payload prefix specified by a uniformly computable parameter. -/
def payloadDrop (p : ℕ → ℕ) (w : Bits) : Bits :=
  DropPrefix.run (unaryField p w ++ splitAdviceHeader false w)

theorem payloadDrop_polytime {p : ℕ → ℕ} (hp : PTimeParam p) :
    PolyTimeComputable (payloadDrop p) :=
  polytime_comp (polytime_append (unaryField_polytime hp) (splitAdviceHeader_polytime false))
    DropPrefix.run_polytime

theorem payloadDrop_encAdvice (p : ℕ → ℕ) (n a : ℕ) (w : Bits) :
    payloadDrop p (encAdvice n a w) = w.drop (p n) := by
  simp only [payloadDrop, unaryField_encAdvice, splitAdviceHeader_encAdvice,
    Bool.false_eq_true, if_false, List.append_assoc, List.singleton_append, DropPrefix.run_replicate]

/-- Recover two unary fields from a random tape whose length encodes a pair. -/
def tapeFirstField (r : Bits) : Bits := unaryParameter (UnpairMachine.decodeWord r) ++ [false]

def tapeSecondField : Bits → Bits := dropUnary ∘ UnpairMachine.decodeWord

theorem tapeFirstField_polytime : PolyTimeComputable tapeFirstField :=
  polytime_comp (polytime_comp UnpairMachine.decodeWord_polytime unaryParameter_polytime)
    polytime_append_false

theorem tapeSecondField_polytime : PolyTimeComputable tapeSecondField :=
  polytime_comp UnpairMachine.decodeWord_polytime dropUnary_polytime

theorem tapeFirstField_of_length_pair (r : Bits) (a b : ℕ) (hr : r.length = Nat.pair a b) :
    tapeFirstField r = List.replicate a true ++ [false] := by
  simp only [tapeFirstField, UnpairMachine.decodeWord_of_length_pair r a b hr, unaryParameter_encAdvice]

theorem tapeSecondField_of_length_pair (r : Bits) (a b : ℕ) (hr : r.length = Nat.pair a b) :
    tapeSecondField r = List.replicate b true ++ [false] := by
  simp only [tapeSecondField, Function.comp_apply, UnpairMachine.decodeWord_of_length_pair r a b hr,
    dropUnary_encAdvice]

/-- Simulate a different polynomially bounded advice function in the exact HILL model. -/
theorem simulateAdvice : SimulateAdviceContract := by
  intro A a b ℓ hb hℓ
  obtain ⟨Y, hY, hTake⟩ := payloadTake ℓ hℓ
  let R := payloadDrop ℓ
  have hR := payloadDrop_polytime hℓ
  let coins := fun n => Nat.pair (b n) (A.coins n)
  let usable := takeUnary ∘ (fun w => (tapeSecondField ∘ R) w ++ R w)
  have hU : PolyTimeComputable usable :=
    polytime_comp (polytime_append (polytime_comp hR tapeSecondField_polytime) hR) takeUnary_polytime
  let input (w : Bits) := ((fun v => v ++ [false]) ∘ unaryParameter) w ++
    ((tapeFirstField ∘ R) w ++ (Y w ++ usable w))
  have hInput : PolyTimeComputable input :=
    polytime_append (polytime_comp unaryParameter_polytime polytime_append_false)
      (polytime_append (polytime_comp hR tapeFirstField_polytime) (polytime_append hY hU))
  let B : Adv := ⟨A.run ∘ input, polytime_comp hInput A.polyTime, coins, isPoly_pair hb A.coinsPoly⟩
  refine ⟨B, ?_⟩
  intro n y hy
  have hyl : y.length = ℓ n := HybridTape.mem_cube_length y (ℓ n) |>.mp hy
  have hbudget : A.coins n ≤ B.coins n := Nat.right_le_pair _ _
  have hEq : ∀ r ∈ cube (B.coins n),
      B.run (encAdvice n (a n) (y ++ r)) =
        A.run (encAdvice n (b n) (y ++ r.take (A.coins n))) := by
    intro r hr
    have hrl : r.length = Nat.pair (b n) (A.coins n) :=
      HybridTape.mem_cube_length r _ |>.mp hr
    have hrUse : A.coins n ≤ r.length := by rw [hrl]; exact hbudget
    let w := encAdvice n (a n) (y ++ r)
    have hwR : R w = r := by
      rw [show R w = (y ++ r).drop (ℓ n) from payloadDrop_encAdvice ℓ n (a n) (y ++ r)]
      simp [← hyl]
    have hwY : Y w = y := by
      have hs : ℓ n ≤ (y ++ r).length := by simp [← hyl]
      rw [show Y w = (y ++ r).take (ℓ n) from hTake n (a n) (y ++ r) hs]
      simp [← hyl]
    have hwU : usable w = r.take (A.coins n) := by
      simp only [usable, Function.comp_apply, hwR, tapeSecondField_of_length_pair r (b n) (A.coins n) hrl,
        List.append_assoc, List.singleton_append, takeUnary_replicate _ _ hrUse]
    change A.run (input w) = _
    apply congrArg A.run
    have hpw : unaryParameter w = List.replicate n true := unaryParameter_encAdvice n (a n) (y ++ r)
    simp only [input, Function.comp_apply, hwR, hwY, hwU, hpw,
      tapeFirstField_of_length_pair r (b n) (A.coins n) hrl]
    simp [encAdvice, enc, List.append_assoc]
  unfold acceptProb
  rw [HybridTape.uniformProb_congr_on (cube (B.coins n))
    (P := fun r => B.run (encAdvice n (a n) (y ++ r)) = [true])
    (Q := fun r => A.run (encAdvice n (b n) (y ++ r.take (A.coins n))) = [true])
    (fun r hr => by rw [hEq r hr])]
  exact HybridTape.uniformProb_take_of_le _ _ hbudget
    (fun r => A.run (encAdvice n (b n) (y ++ r)) = [true])

theorem adviceChange : AdviceChangeContract :=
  InterfaceConsequences.adviceChange_of_simulation simulateAdvice

end HILL.PRG

end HILL416_AdviceSimulation

section HILL416_HybridMachine

set_option backward.isDefEq.respectTransparency.types false

namespace HILL.PRG

open WordCodecs HybridContracts

private def withHeader (Q : Bits → Bits) (w : Bits) : Bits := splitAdviceHeader true w ++ Q w

private theorem withHeader_polytime {Q : Bits → Bits} (hQ : PolyTimeComputable Q) :
    PolyTimeComputable (withHeader Q) :=
  polytime_append (splitAdviceHeader_polytime true) hQ

private theorem withHeader_encAdvice (Q : Bits → Bits) (n a : ℕ) (w : Bits) :
    withHeader Q (encAdvice n a w) = encAdvice n a (Q (encAdvice n a w)) := by
  simp only [withHeader, splitAdviceHeader_encAdvice, if_true]
  simp [encAdvice, enc, List.append_assoc]

private def lengthProductField (f g : Bits → Bits) (w : Bits) : Bits :=
  List.replicate ((f w).length * (g w).length) true ++ [false]

private theorem lengthProductField_polytime {f g : Bits → Bits}
    (hf : PolyTimeComputable f) (hg : PolyTimeComputable g) :
    PolyTimeComputable (lengthProductField f g) :=
  polytime_comp (polytime_unary_product hf hg) polytime_append_false

/-- Splice a single challenge bit string between the W front and the F back. -/
def hybridSplice (F W : FunEns) (a k : ℕ → ℕ) (n i : ℕ) (y u v : Bits) : Bits :=
  (repeatEval W k (a n) n v).take (i * F.ℓ n) ++
    (y ++ (repeatEval F k (a n) n u).drop ((i + 1) * F.ℓ n))

set_option maxHeartbeats 1800000 in
/-- One polynomial-time adversary implements every selected hybrid step. -/
theorem hybridMachine (F W : FunEns) (a k i : ℕ → ℕ)
    (hF : F.PTime a) (hW : W.PTime a) (hL : W.ℓ = F.ℓ)
    (hk : PTimeParam k) (hi : ∀ n, i n ≤ k n) (A : Adv) :
    ∃ B : Adv, ∀ n y, i n < k n → y ∈ cube (F.ℓ n) →
      acceptProb B n a y =
        uniformProb (HybridTape.threeCubes (k n * F.t n) (k n * W.t n) (A.coins n))
          (fun z => A.run (encAdvice n (a n)
            (hybridSplice F W a k n (i n) y z.1.1 z.1.2 ++ z.2)) = [true]) := by
  have hℓ : PTimeParam F.ℓ := hF.2.1
  obtain ⟨hp₀, _, _, RF, hRF, evalF⟩ := repeatPTime F a k hF hk
  obtain ⟨hq₀, _, _, RW, hRW, evalW⟩ := repeatPTime W a k hW hk
  let p := fun n => k n * F.t n
  let q := fun n => k n * W.t n
  have hp : PTimeParam p := hp₀
  have hq : PTimeParam q := hq₀
  have hLP := (parameterArithmetic F.ℓ p hℓ hp).1
  have hPQ := (parameterArithmetic p q hp hq).1
  obtain ⟨Y, hY, eqY⟩ := payloadTake F.ℓ hℓ
  obtain ⟨U, hU, eqU⟩ := payloadSlice F.ℓ p hℓ hp
  obtain ⟨V, hV, eqV⟩ := payloadSlice (fun n => F.ℓ n + p n) q hLP hq
  let R := payloadDrop F.ℓ
  have hR : PolyTimeComputable R := payloadDrop_polytime hℓ
  let index := unaryParameter ∘ tapeFirstField ∘ R
  have hIndex : PolyTimeComputable index :=
    polytime_comp (polytime_comp hR tapeFirstField_polytime) unaryParameter_polytime
  let succIndex (w : Bits) := index w ++ [true]
  have hSucc : PolyTimeComputable succIndex :=
    polytime_append hIndex (polytime_constWord [true])
  let len := unaryParameter ∘ unaryField F.ℓ
  have hLen : PolyTimeComputable len :=
    polytime_comp (unaryField_polytime hℓ) unaryParameter_polytime
  let front := takeUnary ∘ (fun w => lengthProductField index len w ++ (RW ∘ withHeader V) w)
  have hPrefix : PolyTimeComputable front :=
    polytime_comp
      (polytime_append (f := lengthProductField index len) (g := RW ∘ withHeader V)
        (lengthProductField_polytime hIndex hLen)
        (polytime_comp (f := withHeader V) (g := RW) (withHeader_polytime hV) hRW))
      takeUnary_polytime
  let back := DropPrefix.run ∘ (fun w => lengthProductField succIndex len w ++ (RF ∘ withHeader U) w)
  have hSuffix : PolyTimeComputable back :=
    polytime_comp
      (polytime_append (f := lengthProductField succIndex len) (g := RF ∘ withHeader U)
        (lengthProductField_polytime hSucc hLen)
        (polytime_comp (f := withHeader U) (g := RF) (withHeader_polytime hU) hRF))
      DropPrefix.run_polytime
  let usable := takeUnary ∘ (fun w => (tapeSecondField ∘ R) w ++ R w)
  have hUsable : PolyTimeComputable usable :=
    polytime_comp (polytime_append (polytime_comp hR tapeSecondField_polytime) hR) takeUnary_polytime
  let random := DropPrefix.run ∘ (fun w => unaryField (fun n => p n + q n) w ++ usable w)
  have hRandom : PolyTimeComputable random :=
    polytime_comp (polytime_append (unaryField_polytime hPQ) hUsable) DropPrefix.run_polytime
  let out (w : Bits) := front w ++ (Y w ++ (back w ++ random w))
  have hOut : PolyTimeComputable out :=
    polytime_append hPrefix (polytime_append hY (polytime_append hSuffix hRandom))
  let budget (n : ℕ) := p n + q n + A.coins n
  have hBudgetPoly : IsPoly budget :=
    isPoly_of_le (fun n => Nat.add_le_pair (p n + q n) (A.coins n))
      (isPoly_pair (ptimeParamIsPoly _ hPQ) A.coinsPoly)
  let coins (n : ℕ) := Nat.pair (i n) (budget n)
  let B : Adv := ⟨A.run ∘ withHeader out,
    polytime_comp (withHeader_polytime hOut) A.polyTime, coins,
    isPoly_pair (isPoly_of_le hi (ptimeParamIsPoly k hk)) hBudgetPoly⟩
  refine ⟨B, ?_⟩
  intro n y hin hy
  have hyl : y.length = F.ℓ n := HybridTape.mem_cube_length y _ |>.mp hy
  have hbudget : budget n ≤ B.coins n := Nat.right_le_pair _ _
  apply HybridTape.acceptProb_eq_three_of_run A B n a a y (p n) (q n)
    (hybridSplice F W a k n (i n) y) hbudget
  intro r hr
  have hrl : r.length = Nat.pair (i n) (budget n) := HybridTape.mem_cube_length r _ |>.mp hr
  have huse : budget n ≤ r.length := hrl ▸ hbudget
  have hpq : p n + q n ≤ r.length := by
    exact (Nat.le_add_right _ _).trans huse
  let w := encAdvice n (a n) (y ++ r)
  have heR : R w = r := by
    rw [show R w = (y ++ r).drop (F.ℓ n) from payloadDrop_encAdvice _ _ _ _]
    simp [← hyl]
  have heY : Y w = y := by
    have hsize : F.ℓ n ≤ (y ++ r).length := by simp [← hyl]
    rw [show Y w = (y ++ r).take (F.ℓ n) from eqY n _ _ hsize]
    simp [← hyl]
  have heU : U w = r.take (p n) := by
    have hsize : F.ℓ n + p n ≤ (y ++ r).length := by simp only [List.length_append, hyl]; omega
    rw [show U w = ((y ++ r).drop (F.ℓ n)).take (p n) from eqU n _ _ hsize]
    simp [← hyl]
  have heV : V w = (r.drop (p n)).take (q n) := by
    have hsize : F.ℓ n + p n + q n ≤ (y ++ r).length := by simp only [List.length_append, hyl]; omega
    rw [show V w = ((y ++ r).drop (F.ℓ n + p n)).take (q n) from eqV n _ _ hsize]
    rw [← hyl, List.drop_length_add_append]
  have hUc : U w ∈ cube ((repeatEns F k).t n) := by
    exact (HybridTape.mem_cube_length _ _).mpr (by
      rw [heU, List.length_take, Nat.min_eq_left (by omega : p n ≤ r.length)]; rfl)
  have hVc : V w ∈ cube ((repeatEns W k).t n) := by
    exact (HybridTape.mem_cube_length _ _).mpr (by
      rw [heV, List.length_take, List.length_drop, Nat.min_eq_left (by omega : q n ≤ r.length - p n)]; rfl)
  have hI : index w = List.replicate (i n) true := by
    simp only [index, Function.comp_apply, heR,
      tapeFirstField_of_length_pair r (i n) (budget n) hrl]
    exact unaryParameter_replicate _ []
  have hLen' : len w = List.replicate (F.ℓ n) true := by
    have he := unaryField_encAdvice F.ℓ n (a n) (y ++ r)
    simp only [len, Function.comp_apply, w, he]
    exact unaryParameter_replicate _ []
  have hFword : RF (withHeader U w) = repeatEval F k (a n) n (r.take (p n)) := by
    have he := withHeader_encAdvice U n (a n) (y ++ r)
    change RF (withHeader U w) = _
    rw [show withHeader U w = encAdvice n (a n) (U w) from he, (evalF n _ hUc).1, heU]
    rfl
  have hWword : RW (withHeader V w) = repeatEval W k (a n) n ((r.drop (p n)).take (q n)) := by
    have he := withHeader_encAdvice V n (a n) (y ++ r)
    rw [show withHeader V w = encAdvice n (a n) (V w) from he, (evalW n _ hVc).1, heV]
    rfl
  have hPrefixLen : i n * F.ℓ n ≤ (RW (withHeader V w)).length := by
    have h := evalW n _ hVc
    rw [show withHeader V w = encAdvice n (a n) (V w) from withHeader_encAdvice _ _ _ _, h.1, h.2]
    change i n * F.ℓ n ≤ k n * W.ℓ n
    rw [hL]
    exact Nat.mul_le_mul_right _ hin.le
  rw [hWword] at hPrefixLen
  have hePrefix : front w = (repeatEval W k (a n) n ((r.drop (p n)).take (q n))).take (i n * F.ℓ n) := by
    simp only [front, Function.comp_apply, lengthProductField, hI, hLen',
      List.length_replicate, List.append_assoc, List.singleton_append,
      takeUnary_replicate _ _ hPrefixLen, hWword]
  have heSuffix : back w = (repeatEval F k (a n) n (r.take (p n))).drop ((i n + 1) * F.ℓ n) := by
    simp only [back, Function.comp_apply, lengthProductField, succIndex, hI, hLen',
      List.length_append, List.length_cons, List.length_nil, List.length_replicate,
      List.append_assoc, List.singleton_append, DropPrefix.run_replicate, hFword]
  have hUseful : usable w = r.take (budget n) := by
    simp only [usable, Function.comp_apply, heR, tapeSecondField_of_length_pair _ _ _ hrl,
      List.append_assoc, List.singleton_append, takeUnary_replicate _ _ huse]
  have hRandom' : random w = (r.drop (p n + q n)).take (A.coins n) := by
    have hf : unaryField (fun n => p n + q n) w = List.replicate (p n + q n) true ++ [false] :=
      unaryField_encAdvice _ _ _ _
    simp only [random, Function.comp_apply, hf, hUseful,
      List.append_assoc, List.singleton_append, DropPrefix.run_replicate, List.drop_take]
    rw [show budget n - (p n + q n) = A.coins n by simp [budget]]
  change A.run (withHeader out w) = _
  apply congrArg A.run
  rw [show withHeader out w = encAdvice n (a n) (out w) from withHeader_encAdvice _ _ _ _]
  simp only [out, hePrefix, heY, heSuffix, hRandom', hybridSplice, List.append_assoc]

end HILL.PRG

end HILL416_HybridMachine

section HILL416_FiniteAcceptance

namespace HILL.PRG

open scoped BigOperators

theorem sum_lawOn_mul {α β : Type*} [DecidableEq β]
    (S : Finset α) (Y : Finset β) (f : α → β)
    (hY : ∀ x ∈ S, f x ∈ Y) (payoff : β → ℝ) :
    ∑ y ∈ Y, lawOn S f y * payoff y = (∑ x ∈ S, payoff (f x)) / S.card := by
  classical
  have hWeight (y : β) : ((S.filter fun x => f x = y).card : ℝ) * payoff y =
      ∑ x ∈ S, if f x = y then payoff y else 0 := by
    rw [← Finset.sum_filter]
    simp
  simp only [lawOn, div_mul_eq_mul_div, hWeight, ← Finset.sum_div]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  simp [Finset.sum_ite_eq, hY x hx]

theorem uniformProb_eq_sum {α : Type*} [DecidableEq α]
    (S : Finset α) (e : α → Prop) [DecidablePred e] :
    uniformProb S e = (∑ x ∈ S, if e x then (1 : ℝ) else 0) / S.card := by
  simp [uniformProb]

theorem uniformProb_product_average {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (T : Finset β) (e : α → β → Prop) [∀ x, DecidablePred (e x)] :
    uniformProb (S ×ˢ T) (fun p => e p.1 p.2) =
      (∑ x ∈ S, uniformProb T (e x)) / S.card := by
  simp only [uniformProb_eq_sum, Finset.sum_product, Finset.card_product, Nat.cast_mul,
    Finset.sum_div, div_div, mul_comm]

theorem expectedAccept_eq_uniformProb {α : Type*} [DecidableEq α]
    (A : Adv) (a : ℕ → ℕ) (n ℓ : ℕ)
    (S : Finset α) (f : α → Bits) (hF : ∀ x ∈ S, f x ∈ cube ℓ) :
    ∑ y ∈ cube ℓ, lawOn S f y * acceptProb A n a y =
      uniformProb (S ×ˢ cube (A.coins n))
        (fun z => A.run (encAdvice n (a n) (f z.1 ++ z.2)) = [true]) := by
  rw [sum_lawOn_mul S (cube ℓ) f hF]
  exact (uniformProb_product_average S (cube (A.coins n))
    (fun x r => A.run (encAdvice n (a n) (f x ++ r)) = [true])).symm

end HILL.PRG

end HILL416_FiniteAcceptance

section HILL416_HybridProduct

namespace HILL.PRG

open HybridContracts
open scoped BigOperators

private noncomputable def avg {α : Type*} (S : Finset α) (f : α → ℝ) : ℝ :=
  (∑ x ∈ S, f x) / S.card

private theorem avg_congr {α : Type*} (S : Finset α) {f g : α → ℝ}
    (h : ∀ x ∈ S, f x = g x) : avg S f = avg S g := by
  unfold avg
  exact congrArg (· / (S.card : ℝ)) (Finset.sum_congr rfl h)

private theorem avg_const {α : Type*} (S : Finset α) (hS : S.Nonempty) (c : ℝ) :
    avg S (fun _ => c) = c := by
  have h : (S.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hS.card_ne_zero
  simp [avg, nsmul_eq_mul, h, mul_comm]

private theorem avg_product {α β : Type*} (S : Finset α) (T : Finset β) (f : α × β → ℝ) :
    avg (S ×ˢ T) f = avg S (fun x => avg T (fun y => f (x, y))) := by
  simp only [avg, Finset.sum_product, Finset.card_product, Nat.cast_mul, Finset.sum_div, div_div, mul_comm]

private theorem avg_swap {α β : Type*} (S : Finset α) (T : Finset β) (f : α → β → ℝ) :
    avg S (fun x => avg T (fun y => f x y)) =
      avg T (fun y => avg S (fun x => f x y)) := by
  simp only [avg, Finset.sum_div, div_div]
  rw [Finset.sum_comm, mul_comm]

private theorem avg_append (m n : ℕ) (f : Bits → ℝ) :
    avg (cube (m + n)) f = avg (cube m) (fun x => avg (cube n) (fun y => f (x ++ y))) := by
  rw [← avg_product (cube m) (cube n) (fun z : Bits × Bits => f (z.1 ++ z.2))]
  unfold avg
  rw [← HybridTape.cube_append_image m n, Finset.sum_image (HybridTape.append_injOn m n),
    Finset.card_image_iff.mpr (HybridTape.append_injOn m n)]
  rfl

private theorem avg_cube_zero (f : Bits → ℝ) : avg (cube 0) f = f [] := by
  have h : cube 0 = {[]} := by
    ext w
    simp [HybridTape.mem_cube_length]
  simp [h, avg]

private theorem repeatEval_at_count (F : FunEns) (a k : ℕ → ℕ) (n : ℕ) (w : Bits) :
    repeatEval F k (a n) n w = repeatEval F (fun _ => k n) (a n) n w := rfl

private theorem repeatEval_append (F : FunEns) (adv n i j : ℕ)
    (x y : Bits) (h : x.length = i * F.t n) :
    repeatEval F (fun _ => i + j) adv n (x ++ y) =
      repeatEval F (fun _ => i) adv n x ++ repeatEval F (fun _ => j) adv n y := by
  simp only [repeatEval, List.range_add (n := i) (m := j), List.flatMap_append, List.flatMap_map]
  congr 1
  · apply List.flatMap_congr
    intro s hs
    have hs' : s < i := List.mem_range.mp hs
    have hd : s * F.t n ≤ x.length := by
      rw [h]
      exact Nat.mul_le_mul_right _ hs'.le
    rw [List.drop_append_of_le_length hd, List.take_append_of_le_length]
    rw [List.length_drop, h]
    have hb : (s + 1) * F.t n ≤ i * F.t n := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul, Nat.one_mul] at hb
    omega
  · apply List.flatMap_congr
    intro s _
    simp only [Nat.add_mul, ← h, List.drop_length_add_append]

private theorem repeatEval_zero (F : FunEns) (adv n : ℕ) (x : Bits) :
    repeatEval F (fun _ => 0) adv n x = [] := rfl

private theorem repeatEval_one (F : FunEns) (adv n : ℕ) (x : Bits) (hx : x.length = F.t n) :
    repeatEval F (fun _ => 1) adv n x = F.f adv n x := by
  simp [repeatEval, ← hx]

private theorem avg_repeat_take (F : FunEns) (a : ℕ → ℕ) (n i k : ℕ)
    (hi : i ≤ k) (hLen : ∀ x ∈ cube (F.t n), (F.f (a n) n x).length = F.ℓ n)
    (test : Bits → ℝ) :
    avg (cube (k * F.t n)) (fun x =>
      test ((repeatEval F (fun _ => k) (a n) n x).take (i * F.ℓ n))) =
    avg (cube (i * F.t n)) (fun x => test (repeatEval F (fun _ => i) (a n) n x)) := by
  have hk : i + (k - i) = k := Nat.add_sub_of_le hi
  have hWidth : k * F.t n = i * F.t n + (k - i) * F.t n := by
    rw [← Nat.add_mul, hk]
  rw [hWidth, avg_append]
  apply avg_congr
  intro x hx
  have hx' := (HybridTape.mem_cube_length _ _).mp hx
  have hOut := repeatEval_length F a (fun _ => i) n hLen x hx
  have he (y : Bits) :
      (repeatEval F (fun _ => k) (a n) n (x ++ y)).take (i * F.ℓ n) =
        repeatEval F (fun _ => i) (a n) n x := by
    rw [← hk, repeatEval_append F _ _ i (k - i) x y hx']
    exact List.take_left' hOut
  simp only [he]
  exact avg_const _ (HybridTape.cube_nonempty _) _

private theorem avg_repeat_drop (F : FunEns) (a : ℕ → ℕ) (n i k : ℕ)
    (hi : i ≤ k) (hLen : ∀ x ∈ cube (F.t n), (F.f (a n) n x).length = F.ℓ n)
    (test : Bits → ℝ) :
    avg (cube (k * F.t n)) (fun x =>
      test ((repeatEval F (fun _ => k) (a n) n x).drop (i * F.ℓ n))) =
    avg (cube ((k - i) * F.t n)) (fun x =>
      test (repeatEval F (fun _ => k - i) (a n) n x)) := by
  have hk : i + (k - i) = k := Nat.add_sub_of_le hi
  have hWidth : k * F.t n = i * F.t n + (k - i) * F.t n := by
    rw [← Nat.add_mul, hk]
  rw [hWidth, avg_append]
  trans avg (cube (i * F.t n)) (fun _ =>
    avg (cube ((k - i) * F.t n)) (fun x => test (repeatEval F (fun _ => k - i) (a n) n x)))
  · apply avg_congr
    intro x hx
    have hx' := (HybridTape.mem_cube_length _ _).mp hx
    have hOut := repeatEval_length F a (fun _ => i) n hLen x hx
    apply avg_congr
    intro y _
    rw [← hk, repeatEval_append F _ _ i (k - i) x y hx', ← hOut]
    simp only [List.drop_left, hk]
  · exact avg_const _ (HybridTape.cube_nonempty _) _

private noncomputable def stepAverage (A : Adv) (F W : FunEns) (a k : ℕ → ℕ)
    (n i : ℕ) (y : Bits) : ℝ :=
  avg (cube (i * W.t n)) fun v =>
    avg (cube ((k n - (i + 1)) * F.t n)) fun u =>
      acceptProb A n a
        (repeatEval W (fun _ => i) (a n) n v ++
          (y ++ repeatEval F (fun _ => k n - (i + 1)) (a n) n u))

private noncomputable def hybridAverage (A : Adv) (F W : FunEns) (a k : ℕ → ℕ)
    (n i : ℕ) : ℝ :=
  avg (cube (i * W.t n)) fun v =>
    avg (cube ((k n - i) * F.t n)) fun u =>
      acceptProb A n a
        (repeatEval W (fun _ => i) (a n) n v ++ repeatEval F (fun _ => k n - i) (a n) n u)

private theorem fullSplice_eq_stepAverage (A : Adv) (F W : FunEns) (a k : ℕ → ℕ)
    (n i : ℕ) (hi : i < k n) (hL : W.ℓ n = F.ℓ n)
    (hF : ∀ x ∈ cube (F.t n), (F.f (a n) n x).length = F.ℓ n)
    (hW : ∀ x ∈ cube (W.t n), (W.f (a n) n x).length = W.ℓ n)
    (y : Bits) :
    uniformProb (HybridTape.threeCubes (k n * F.t n) (k n * W.t n) (A.coins n))
      (fun z => A.run (encAdvice n (a n)
        (hybridSplice F W a k n i y z.1.1 z.1.2 ++ z.2)) = [true]) =
      stepAverage A F W a k n i y := by
  unfold HybridTape.threeCubes
  let S := cube (k n * F.t n)
  let T := cube (k n * W.t n)
  have he := uniformProb_product_average (S.product T) (cube (A.coins n))
    (fun (z : Bits × Bits) r =>
      A.run (encAdvice n (a n) (hybridSplice F W a k n i y z.1 z.2 ++ r)) = [true])
  refine he.trans ?_
  change avg (S ×ˢ T) (fun z => acceptProb A n a (hybridSplice F W a k n i y z.1 z.2)) = _
  rw [avg_product, avg_swap]
  simp only [S, T, hybridSplice, repeatEval_at_count]
  have hDrop (z : Bits) :
      avg (cube (k n * F.t n)) (fun u =>
        acceptProb A n a (z ++ (y ++
          (repeatEval F (fun _ => k n) (a n) n u).drop ((i + 1) * F.ℓ n)))) =
      avg (cube ((k n - (i+1)) * F.t n)) (fun u =>
        acceptProb A n a (z ++ (y ++ repeatEval F (fun _ => k n - (i + 1)) (a n) n u))) :=
    avg_repeat_drop F a n (i+1) (k n) hi hF (fun u => acceptProb A n a (z ++ (y ++ u)))
  simp only [hDrop]
  let test (z : Bits) := avg (cube ((k n - (i+1)) * F.t n)) (fun u =>
    acceptProb A n a (z ++ (y ++ repeatEval F (fun _ => k n - (i + 1)) (a n) n u)))
  have ht := avg_repeat_take W a n i (k n) hi.le hW test
  rw [hL] at ht
  exact ht

private theorem avg_F_step (A : Adv) (F W : FunEns) (a k : ℕ → ℕ)
    (n i : ℕ) (hi : i < k n) :
    avg (cube (F.t n)) (fun x => stepAverage A F W a k n i (F.f (a n) n x)) =
      hybridAverage A F W a k n i := by
  unfold stepAverage hybridAverage
  rw [avg_swap]
  apply avg_congr
  intro v _
  have hCount : k n - i = 1 + (k n - (i + 1)) := by omega
  have hWidth : (k n - i) * F.t n = F.t n + (k n - (i + 1)) * F.t n := by
    rw [hCount, Nat.add_mul, Nat.one_mul]
  rw [hWidth, avg_append]
  apply avg_congr
  intro x hx
  apply avg_congr
  intro u _
  have hx' : x.length = F.t n := (HybridTape.mem_cube_length _ _).mp hx
  have h := repeatEval_append F (a n) n 1 (k n - (i+1)) x u (by simpa only [Nat.one_mul] using hx')
  have hsplit : repeatEval F (fun _ => k n - i) (a n) n (x ++ u) =
      F.f (a n) n x ++ repeatEval F (fun _ => k n - (i+1)) (a n) n u := by
    rw [← repeatEval_one F (a n) n x hx']
    exact hCount.symm ▸ h
  rw [hsplit]

private theorem avg_W_step (A : Adv) (F W : FunEns) (a k : ℕ → ℕ)
    (n i : ℕ) :
    avg (cube (W.t n)) (fun x => stepAverage A F W a k n i (W.f (a n) n x)) =
      hybridAverage A F W a k n (i+1) := by
  unfold stepAverage hybridAverage
  rw [avg_swap]
  have hWidth : (i+1) * W.t n = i * W.t n + W.t n := by rw [Nat.add_mul, Nat.one_mul]
  rw [hWidth, avg_append]
  apply avg_congr
  intro v hv
  apply avg_congr
  intro x hx
  have hv' : v.length = i * W.t n := (HybridTape.mem_cube_length _ _).mp hv
  have hx' : x.length = W.t n := (HybridTape.mem_cube_length _ _).mp hx
  simp only [repeatEval_append W (a n) n i 1 v x hv', repeatEval_one W (a n) n x hx',
    List.append_assoc]

private theorem hybridAverage_zero (A : Adv) (F W : FunEns) (a k : ℕ → ℕ)
    (n : ℕ) (hF : ∀ x ∈ cube (F.t n), (F.f (a n) n x).length = F.ℓ n) :
    hybridAverage A F W a k n 0 =
      ∑ y ∈ cube (k n * F.ℓ n), repeatLaw F a k n y * acceptProb A n a y := by
  unfold hybridAverage repeatLaw
  simp only [Nat.zero_mul, avg_cube_zero, repeatEval_zero, List.nil_append, Nat.sub_zero]
  exact (sum_lawOn_mul _ _ _ (fun x hx => (HybridTape.mem_cube_length _ _).mpr
    (repeatEval_length F a k n hF x hx)) _).symm

private theorem hybridAverage_end (A : Adv) (F W : FunEns) (a k : ℕ → ℕ)
    (n : ℕ) (hL : W.ℓ n = F.ℓ n)
    (hW : ∀ x ∈ cube (W.t n), (W.f (a n) n x).length = W.ℓ n) :
    hybridAverage A F W a k n (k n) =
      ∑ y ∈ cube (k n * F.ℓ n), repeatLaw W a k n y * acceptProb A n a y := by
  unfold hybridAverage repeatLaw
  simp only [Nat.sub_self, Nat.zero_mul, avg_cube_zero, repeatEval_zero, List.append_nil, ← hL]
  exact (sum_lawOn_mul _ _ _ (fun x hx => (HybridTape.mem_cube_length _ _).mpr
    (repeatEval_length W a k n hW x hx)) _).symm


set_option maxHeartbeats 1000000 in
/-- Independent repetition preserves computational indistinguishability with the usual
factor equal to the number of repetitions. The simulator is one uniform adversary. -/
theorem productHybrid : ProductHybridContract := by
  intro F W a k hF hW hL hk A
  classical
  let p := hybridAverage A F W a k
  have hSel (n : ℕ) : ∃ i : ℕ, i ≤ k n ∧
      (0 < k n → i < k n ∧
        |p n (k n) - p n 0| ≤ (k n : ℝ) * |p n (i + 1) - p n i|) := by
    by_cases h : 0 < k n
    · obtain ⟨i, hi, hb⟩ := hybridStepSelection (p n) (k n) h
      exact ⟨i, hi.le, fun _ => ⟨hi, hb⟩⟩
    · exact ⟨0, Nat.zero_le _, fun hn => (h hn).elim⟩
  choose i hi hGap using hSel
  obtain ⟨B, hB⟩ := hybridMachine F W a k i hF hW hL hk hi A
  refine ⟨B, ?_⟩
  intro n
  have hFL (x : Bits) (hx : x ∈ cube (F.t n)) : (F.f (a n) n x).length = F.ℓ n := by
    obtain ⟨_, _, _, _, _, h⟩ := hF
    exact (h n x hx).2
  have hWL (x : Bits) (hx : x ∈ cube (W.t n)) : (W.f (a n) n x).length = W.ℓ n := by
    obtain ⟨_, _, _, _, _, h⟩ := hW
    exact (h n x hx).2
  have hL' : W.ℓ n = F.ℓ n := congrFun hL n
  have hEnds : advantage A n a (k n * F.ℓ n) (repeatLaw F a k n) (repeatLaw W a k n) =
      |p n (k n) - p n 0| := by
    unfold advantage
    simp only [sub_mul, Finset.sum_sub_distrib, p]
    rw [← hybridAverage_zero A F W a k n hFL, ← hybridAverage_end A F W a k n hL' hWL, abs_sub_comm]
  rw [hEnds]
  by_cases hn : 0 < k n
  · obtain ⟨hin, hb⟩ := hGap n hn
    have hAcc (y : Bits) (hy : y ∈ cube (F.ℓ n)) :
        acceptProb B n a y = stepAverage A F W a k n (i n) y :=
      (hB n y hin hy).trans (fullSplice_eq_stepAverage A F W a k n (i n) hin hL' hFL hWL y)
    have hMapsF : ∀ x ∈ cube (F.t n), F.f (a n) n x ∈ cube (F.ℓ n) :=
      fun x hx => (HybridTape.mem_cube_length _ _).mpr (hFL x hx)
    have hMapsW : ∀ x ∈ cube (W.t n), W.f (a n) n x ∈ cube (F.ℓ n) :=
      fun x hx => (HybridTape.mem_cube_length _ _).mpr ((hWL x hx).trans hL')
    have hFA : ∑ y ∈ cube (F.ℓ n), F.law a n y * acceptProb B n a y = p n (i n) := by
      unfold FunEns.law
      rw [sum_lawOn_mul _ _ _ hMapsF]
      change avg (cube (F.t n)) (fun x => acceptProb B n a (F.f (a n) n x)) = _
      exact (avg_congr _ (fun x hx => hAcc _ (hMapsF x hx))).trans (avg_F_step A F W a k n (i n) hin)
    have hWA : ∑ y ∈ cube (F.ℓ n), W.law a n y * acceptProb B n a y = p n (i n+1) := by
      unfold FunEns.law
      rw [sum_lawOn_mul _ _ _ hMapsW]
      change avg (cube (W.t n)) (fun x => acceptProb B n a (W.f (a n) n x)) = _
      exact (avg_congr _ (fun x hx => hAcc _ (hMapsW x hx))).trans (avg_W_step A F W a k n (i n))
    have hStep : advantage B n a (F.ℓ n) (F.law a n) (W.law a n) =
        |p n (i n + 1) - p n (i n)| := by
      unfold advantage
      simp only [sub_mul, Finset.sum_sub_distrib, hFA, hWA]
      exact abs_sub_comm _ _
    rwa [hStep]
  · have hz : k n = 0 := Nat.eq_zero_of_not_pos hn
    simp [hz]

theorem productCompIndist : ProductCompIndistContract :=
  productCompIndist_of_simulator productHybrid


open ConstructionContracts in
/-- Acceptance against an ideal sampler factors through its repeated output and the two independent fields. -/
theorem expectation_ideal_eq (F : FunEns) (a k N j : ℕ → ℕ) (A B : Adv)
    (n : ℕ) (hj : j n ≤ N n)
    (hY : ∀ x ∈ cube (k n * F.t n), repeatEval F k (a n) n x ∈ cube (k n * F.ℓ n))
    (hI : ∀ x ∈ cube ((idealGenerator F k N).t n),
      (idealGenerator F k N).f (packAdvice a j n) n x ∈ cube ((idealGenerator F k N).ℓ n))
    (hB : ∀ y ∈ cube (k n * F.ℓ n),
      acceptProb B n (packAdvice a j) y =
        uniformProb (HybridTape.threeCubes (N n) (keyWidth (N n)) (A.coins n))
          (fun z => A.run (encAdvice n (packAdvice a j n)
            (y ++ (padPrefix (N n) (j n) z.1.1 ++ (z.1.2 ++ z.2)))) = [true])) :
    (∑ y ∈ cube ((idealGenerator F k N).ℓ n),
      (idealGenerator F k N).law (packAdvice a j) n y * acceptProb A n (packAdvice a j) y) =
      ∑ y ∈ cube (k n * F.ℓ n), repeatLaw F a k n y * acceptProb B n (packAdvice a j) y := by
  unfold FunEns.law repeatLaw
  rw [sum_lawOn_mul _ _ _ hI, sum_lawOn_mul _ _ _ hY]
  change avg (cube (k n * F.t n + N n + keyWidth (N n)))
    (fun w => acceptProb A n (packAdvice a j) ((idealGenerator F k N).f (packAdvice a j n) n w)) =
      avg (cube (k n * F.t n)) (fun x => acceptProb B n (packAdvice a j) (repeatEval F k (a n) n x))
  rw [avg_append (k n * F.t n + N n) (keyWidth (N n)), avg_append (k n * F.t n) (N n)]
  apply avg_congr
  intro x hx
  let y := repeatEval F k (a n) n x
  rw [show acceptProb B n (packAdvice a j) y = _ from hB y (hY x hx)]
  have hp := uniformProb_product_average ((cube (N n)).product (cube (keyWidth (N n))))
    (cube (A.coins n)) (fun (z : Bits × Bits) r =>
      A.run (encAdvice n (packAdvice a j n) (y ++ (padPrefix (N n) (j n) z.1 ++ (z.2 ++ r)))) = [true])
  refine Eq.trans ?_ hp.symm
  have hCoins (z : Bits × Bits) :
      uniformProb (cube (A.coins n)) (fun r =>
        A.run (encAdvice n (packAdvice a j n) (y ++ (padPrefix (N n) (j n) z.1 ++ (z.2 ++ r)))) = [true]) =
      acceptProb A n (packAdvice a j) (y ++ (padPrefix (N n) (j n) z.1 ++ z.2)) := by
    simp only [acceptProb, List.append_assoc]
  simp only [hCoins]
  have hProd : ((cube (N n)).product (cube (keyWidth (N n)))) =
      cube (N n) ×ˢ cube (keyWidth (N n)) := rfl
  change _ = avg ((cube (N n)).product (cube (keyWidth (N n))))
    (fun z => acceptProb A n (packAdvice a j) (y ++ (padPrefix (N n) (j n) z.1 ++ z.2)))
  rw [hProd, avg_product]
  apply avg_congr
  intro z hz
  apply avg_congr
  intro r hr
  have hxl : x.length = k n * F.t n := (HybridTape.mem_cube_length _ _).mp hx
  have hzl : z.length = N n := (HybridTape.mem_cube_length _ _).mp hz
  have hrl : r.length = keyWidth (N n) := (HybridTape.mem_cube_length _ _).mp hr
  have h1 : (x ++ (z ++ r)).take (k n * F.t n) = x := List.take_left' hxl
  have h2 : ((x ++ (z ++ r)).drop (k n * F.t n)).take (N n) = z := by
    rw [← hxl, List.drop_left, List.take_left' hzl]
  have h3 : ((x ++ (z ++ r)).drop (k n * F.t n + N n)).take (keyWidth (N n)) = r := by
    have hs : k n * F.t n + N n = x.length + z.length := by rw [hxl, hzl]
    rw [hs, List.drop_length_add_append, List.drop_left, ← hrl]
    exact List.take_length
  simp only [idealGenerator, packAdvice, Nat.unpair_pair, Nat.min_eq_left hj, List.append_assoc,
    h1, h2, h3, y]

end HILL.PRG

end HILL416_HybridProduct

section HILL416_Decorator

set_option backward.isDefEq.respectTransparency.types false

namespace HILL.PRG

open WordCodecs ConstructionContracts HybridContracts

private def payloadEns (L : ℕ → ℕ) : FunEns where
  t := L
  ℓ := L
  f _ _ x := x

private theorem payloadEnsPTime (L a : ℕ → ℕ) (hL : PTimeParam L) (ha : IsPoly a) :
    (payloadEns L).PTime a := by
  refine ⟨hL, hL, ha, splitAdviceHeader false, splitAdviceHeader_polytime false, ?_⟩
  intro n x hx
  refine ⟨?_, (HybridTape.mem_cube_length _ _).mp hx⟩
  simp only [payloadEns, splitAdviceHeader_encAdvice, if_false, Bool.false_eq_true]

set_option maxHeartbeats 1000000 in
/-- Sample the extra fields independently and feed the resulting word to the given adversary. -/
theorem decorateAdversary (L N a j : ℕ → ℕ) (hL : PTimeParam L) (hN : PTimeParam N)
    (ha : IsPoly a) (hj : ∀ n, j n ≤ N n) (A : Adv) :
    ∃ B : Adv, ∀ n y, y ∈ cube (L n) →
      acceptProb B n (packAdvice a j) y =
        uniformProb (HybridTape.threeCubes (N n) (keyWidth (N n)) (A.coins n))
          (fun z => A.run (encAdvice n (packAdvice a j n)
            (y ++ (padPrefix (N n) (j n) z.1.1 ++ (z.1.2 ++ z.2)))) = [true]) := by
  let D := idealGenerator (payloadEns L) (fun _ => 1) N
  let p := fun n => keyWidth (N n)
  let Lall := fun n => L n + N n + p n
  let coins := fun n => N n + p n + A.coins n
  obtain ⟨hT, _, _, DRun, hDRun, hD⟩ :=
    idealGeneratorPTime (payloadEns L) a (fun _ => 1) N j (payloadEnsPTime L a hL ha)
      onePTimeParam hN hj
  have hAll : PTimeParam Lall := by
    simpa only [D, idealGenerator, payloadEns, Nat.one_mul, Lall, p] using hT
  have hNP := (parameterArithmetic N p hN (keyWidthPTime hN)).1
  have hCoins : IsPoly coins :=
    isPoly_of_le (fun n => Nat.add_le_pair (N n + p n) (A.coins n))
      (isPoly_pair (ptimeParamIsPoly _ hNP) A.coinsPoly)
  let keep := splitAdviceHeader true
  have hKeep : PolyTimeComputable keep := splitAdviceHeader_polytime true
  obtain ⟨X, hX, hTake⟩ := payloadTake Lall hAll
  let forD (w : Bits) := keep w ++ X w
  have hForD : PolyTimeComputable forD := polytime_append hKeep hX
  let input (w : Bits) := keep w ++ ((DRun ∘ forD) w ++ payloadDrop Lall w)
  have hInput : PolyTimeComputable input :=
    polytime_append hKeep (polytime_append
      (polytime_comp (f := forD) (g := DRun) hForD hDRun) (payloadDrop_polytime hAll))
  let B : Adv := ⟨A.run ∘ input, polytime_comp hInput A.polyTime, coins, hCoins⟩
  refine ⟨B, ?_⟩
  intro n y hy
  let b := packAdvice a j
  have hyl : y.length = L n := (HybridTape.mem_cube_length _ _).mp hy
  let assemble (z r : Bits) := y ++ (padPrefix (N n) (j n) z ++ r)
  have h := HybridTape.acceptProb_eq_three_of_run A B n b b y (N n) (p n)
    assemble (by rfl) ?_
  · simpa only [b, assemble, p, List.append_assoc] using h
  intro r hr
  have hrl : r.length = N n + p n + A.coins n := (HybridTape.mem_cube_length _ _).mp hr
  let w := encAdvice n (b n) (y ++ r)
  let z := r.take (N n)
  let key := (r.drop (N n)).take (p n)
  have hzl : z.length = N n := by
    simp only [z, List.length_take, hrl, Nat.min_eq_left (show N n ≤ N n + p n + A.coins n by omega)]
  have hkl : key.length = p n := by
    simp only [key, List.length_take, List.length_drop, hrl]
    omega
  have hsz : Lall n ≤ (y ++ r).length := by
    simp only [Lall, List.length_append, hyl, hrl]
    omega
  have hrTake : r.take (N n + p n) = z ++ key := by
    have ht : (r.take (N n + p n)).take (N n) = z := by
      simp only [List.take_take, Nat.min_eq_left (Nat.le_add_right _ _), z]
    change r.take (N n + p n) = z ++ (r.drop (N n)).take (p n)
    rw [← List.take_append_drop (N n) (r.take (N n + p n)), ht, List.drop_take,
      Nat.add_sub_cancel_left]
  have hWidth : Lall n = y.length + (N n + p n) := by simp only [Lall, hyl, Nat.add_assoc]
  have hX' : X w = y ++ (z ++ key) := by
    rw [show X w = (y ++ r).take (Lall n) from hTake n _ _ hsz, List.take_append, hWidth,
      Nat.add_sub_cancel_left, hrTake, List.take_of_length_le (Nat.le_add_right _ _)]
  have hKeep' : keep w = encAdvice n (b n) [] := by
    simp only [keep, w, splitAdviceHeader_encAdvice, if_true]
  have hForD' : forD w = encAdvice n (b n) (y ++ (z ++ key)) := by
    simp only [forD, hKeep', hX']
    simp [encAdvice, enc, List.append_assoc]
  have hValid : y ++ (z ++ key) ∈ cube (D.t n) := by
    apply (HybridTape.mem_cube_length _ _).mpr
    simp only [D, idealGenerator, payloadEns, Nat.one_mul, List.length_append, hyl, hzl, hkl, p,
      Nat.add_assoc]
  have hDrop' : payloadDrop Lall w = (r.drop (N n + p n)).take (A.coins n) := by
    rw [show payloadDrop Lall w = (y ++ r).drop (Lall n) from payloadDrop_encAdvice _ _ _ _]
    have he : Lall n = y.length + (N n + p n) := by simp only [Lall, hyl, Nat.add_assoc]
    rw [he, List.drop_length_add_append, List.take_of_length_le]
    simp only [List.length_drop, hrl, Nat.add_sub_cancel_left, le_refl]
  have hEval : DRun (forD w) = assemble z key := by
    rw [hForD', (hD n _ hValid).1]
    have h1 : (y ++ (z ++ key)).take (L n) = y := List.take_left' hyl
    have h2 : ((y ++ (z ++ key)).drop (L n)).take (N n) = z := by
      rw [← hyl, List.drop_left, List.take_left' hzl]
    have h3 : ((y ++ (z ++ key)).drop (L n + N n)).take (p n) = key := by
      rw [← hyl, List.drop_length_add_append, ← hzl, List.drop_left, ← hkl]
      exact List.take_length
    have hrep : repeatEval (payloadEns L) (fun _ => 1) (a n) n y = y := by
      simp [repeatEval, payloadEns, ← hyl]
    simp only [payloadEns] at hrep
    simp only [idealGenerator, payloadEns, Nat.one_mul, packAdvice, Nat.unpair_pair,
      Nat.min_eq_left (hj n), h1, h2, h3, p, hrep, assemble, List.append_assoc]
  change A.run (input w) = _
  apply congrArg A.run
  simp only [input, hKeep', Function.comp_apply, hEval, hDrop', assemble, z, key]
  simp [encAdvice, enc, List.append_assoc]

end HILL.PRG

end HILL416_Decorator

section HILL416_ConstructionIndist

namespace HILL.PRG

open HybridContracts ConstructionContracts
open scoped BigOperators

set_option maxHeartbeats 1000000 in
/-- The two padded ideal laws inherit computational indistinguishability. -/
theorem constructionCompIndist : ConstructionCompIndistContract := by
  intro F W a k j hF hW hEq hk hj hCI
  let N := seedWidth F k
  let L := fun n => k n * F.ℓ n
  let b := packAdvice a j
  have hN : PTimeParam N := (parameterArithmetic k F.t hk hF.1).2
  have hL : PTimeParam L := (parameterArithmetic k F.ℓ hk hF.2.1).2
  have hb : IsPoly b := packAdvice_isPoly hF.2.2.1 hN hj
  have hProd := productCompIndist F W a k hF hW hEq hk hCI
  have hShift := adviceChange a b L (repeatLaw F a k) (repeatLaw W a k) hb hL hProd
  intro A
  obtain ⟨B, hB⟩ := decorateAdversary L N a j hL hN hF.2.2.1 hj A
  have hExp (X : FunEns) (hX : X.PTime a) (hEqX : X.ℓ = F.ℓ) (n : ℕ) :
      (∑ y ∈ cube ((hashGenerator F k).ℓ n),
        (idealGenerator X k N).law b n y * acceptProb A n b y) =
        ∑ y ∈ cube (L n), repeatLaw X a k n y * acceptProb B n b y := by
    have hLen (x : Bits) (hx : x ∈ cube (X.t n)) : (X.f (a n) n x).length = X.ℓ n := by
      obtain ⟨_, _, _, _, _, hxRun⟩ := hX
      exact (hxRun n x hx).2
    have hY (x : Bits) (hx : x ∈ cube (k n * X.t n)) :
        repeatEval X k (a n) n x ∈ cube (k n * X.ℓ n) :=
      (HybridTape.mem_cube_length _ _).mpr (repeatEval_length X a k n hLen x hx)
    have hI (x : Bits) (hx : x ∈ cube ((idealGenerator X k N).t n)) :
        (idealGenerator X k N).f (b n) n x ∈ cube ((idealGenerator X k N).ℓ n) := by
      obtain ⟨_, _, _, _, _, hxRun⟩ := idealGeneratorPTime X a k N j hX hk hN hj
      exact (HybridTape.mem_cube_length _ _).mpr (hxRun n x hx).2
    have he := expectation_ideal_eq X a k N j A B n (hj n) hY hI
      (fun y hy => hB n y (by simpa only [L, hEqX] using hy))
    simpa only [idealGenerator, hashGenerator, hEqX, L, N, b] using he
  have hAdv (n : ℕ) :
      advantage A n b ((hashGenerator F k).ℓ n)
        ((idealGenerator F k N).law b n) ((idealGenerator W k N).law b n) =
      advantage B n b (L n) (repeatLaw F a k n) (repeatLaw W a k n) := by
    unfold advantage
    simp only [sub_mul, Finset.sum_sub_distrib, hExp F hF rfl n, hExp W hW hEq n]
  change Negligible (fun n => advantage A n b ((hashGenerator F k).ℓ n)
    ((idealGenerator F k N).law b n) ((idealGenerator W k N).law b n))
  rw [funext hAdv]
  exact hShift B

end HILL.PRG

end HILL416_ConstructionIndist

section HILL416_AffineRowsMachine

set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace HILL.PRG.AffineRowsMachine

open Turing StateTransition MachineContracts

noncomputable section

inductive Tape
  | input | count | seed | scratch | outRev | output
  deriving DecidableEq, Fintype

inductive Label
  | count | seedTag | seedBit | nextRow | row | restore | clearInput | clearSeed | emit
  deriving DecidableEq, Fintype

private abbrev Γ : Tape → Type := fun _ => Bool
private abbrev Stmt := TM2.Stmt Γ Label (Option Bool)
private abbrev Cfg := TM2.Cfg Γ Label (Option Bool)

private def jump (l : Label) : Stmt := .load (fun _ => none) (.goto (fun _ => l))
private def push (t : Tape) (b : Bool) (next : Stmt) : Stmt := .push t (fun _ => b) next
private def pop (t : Tape) (empty : Stmt) (bit : Bool → Stmt) : Stmt :=
  .pop t (fun _ b => b)
    (.branch Option.isSome (.branch (fun b => b.getD false) (bit true) (bit false)) empty)

private def emitBit (b : Bool) (next : Stmt) : Stmt :=
  push .outRev true (push .outRev b next)

private def program : Label → Stmt
  | .count => pop .input (jump .seedTag) (fun b =>
    if b then push .count true (jump .count) else jump .seedTag)
  | .seedTag => pop .input (jump .nextRow) (fun b =>
    if b then jump .seedBit else jump .nextRow)
  | .seedBit => pop .input (jump .nextRow) (fun b => push .seed b (jump .seedTag))
  | .nextRow => pop .count (jump .clearInput) (fun _ =>
    pop .input (emitBit false (jump .row)) (fun b => emitBit b (jump .row)))
  | .row => pop .seed (push .outRev false (jump .restore)) (fun b =>
    pop .input (emitBit false (emitBit b (push .scratch b (jump .row))))
      (fun c => emitBit c (emitBit b (push .scratch b (jump .row)))))
  | .restore => pop .scratch (jump .nextRow) (fun b => push .seed b (jump .restore))
  | .clearInput => pop .input (jump .clearSeed) (fun _ => jump .clearInput)
  | .clearSeed => pop .seed (jump .emit) (fun _ => jump .clearSeed)
  | .emit => pop .outRev (.load (fun _ => none) .halt) (fun b => push .output b (jump .emit))

private def stk (r c x s rev out : Bits) : Tape → Bits
  | .input => r
  | .count => c
  | .seed => x
  | .scratch => s
  | .outRev => rev
  | .output => out

private def cfg (l : Label) (r c x s rev out : Bits) : Cfg := ⟨some l, none, stk r c x s rev out⟩
private def done (out : Bits) : Cfg := ⟨none, none, stk [] [] [] [] [] out⟩

private def machine : FinTM2 where
  K := Tape
  k₀ := .input
  k₁ := .output
  Γ := Γ
  Λ := Label
  main := .count
  σ := Option Bool
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := program

private abbrev step := TM2.step program
private abbrev Run (x y : Cfg) (n : ℕ) := EvalsToInTime step x (some y) n
private def one {x y : Cfg} (h : step x = some y) : Run x y 1 := ⟨⟨1, h⟩, le_rfl⟩
private def seq {a b c : Cfg} {m n : ℕ} (x : Run a b m) (y : Run b c n) : Run a c (m+n) :=
  ⟨(EvalsToInTime.trans _ _ _ _ _ _ x y).toEvalsTo,
    (Nat.add_le_add y.steps_le_m x.steps_le_m).trans_eq (Nat.add_comm _ _)⟩

private def relax {a b : Cfg} {m n : ℕ} (h : Run a b m) (hle : m ≤ n) : Run a b n :=
  ⟨h.toEvalsTo, h.steps_le_m.trans hle⟩

private def readCount : Bits → ℕ × Bits
  | [] => (0, [])
  | false :: xs => (0, xs)
  | true :: xs => ((readCount xs).1 + 1, (readCount xs).2)

private theorem readCount_size (w : Bits) : (readCount w).1 + (readCount w).2.length ≤ w.length := by
  induction w with
  | nil => rfl
  | cons b xs ih =>
    cases b with
    | false => simp [readCount]
    | true => simp only [readCount, List.length_cons]; omega

private theorem readCount_spec (j : ℕ) (w : Bits) :
    readCount (enc j w) = (j, w) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change ((readCount (enc j w)).1 + 1, (readCount (enc j w)).2) = (j+1, w)
    rw [ih]

private def readSeed : Bits → Bits × Bits
  | true :: b :: xs => ((readSeed xs).1 ++ [b], (readSeed xs).2)
  | false :: xs => ([], xs)
  | _ => ([], [])

private theorem readSeed_size (w : Bits) : 2 * (readSeed w).1.length + (readSeed w).2.length ≤ w.length := by
  induction w using List.twoStepInduction with
  | nil => rfl
  | singleton b => cases b <;> decide
  | cons_cons a b xs ih _ =>
    cases a with
    | false => simp [readSeed]
    | true => simp only [readSeed, List.length_append, List.length_singleton, List.length_cons, List.length_nil]; omega

private theorem readSeed_spec (x r : Bits) :
    readSeed (quoteBits x ++ false :: r) = (x.reverse, r) := by
  induction x with
  | nil => rfl
  | cons b xs ih =>
    change ((readSeed (quoteBits xs ++ false :: r)).1 ++ [b],
      (readSeed (quoteBits xs ++ false :: r)).2) = (List.reverse (b :: xs), r)
    rw [ih, List.reverse_cons]

private def rowData : Bits → Bits → Bits
  | [], _ => []
  | b :: xs, r => r.headD false :: b :: rowData xs r.tail

private def rows (x : Bits) : ℕ → Bits → List Bits
  | 0, _ => []
  | j + 1, r => (r.headD false :: rowData x r.tail) :: rows x j (r.drop (x.length + 1))

private def formatted (x : Bits) (j : ℕ) (r : Bits) : Bits :=
  encodeWords (rows x j r)

def format (w : Bits) : Bits :=
  let c := readCount w
  let q := readSeed c.2
  formatted q.1 c.1 q.2

private theorem countTrue (w c : Bits) :
    step (cfg .count (true :: w) c [] [] [] []) = some (cfg .count w (true :: c) [] [] [] []) := by
  (simp [cfg, done, stk, program, pop, push, jump, emitBit, Function.update] <;>
    (funext k; cases k <;> simp [stk, Function.update]))

private theorem countFalse (w c : Bits) :
    step (cfg .count (false :: w) c [] [] [] []) = some (cfg .seedTag w c [] [] [] []) := by
  (simp [cfg, done, stk, program, pop, push, jump, emitBit, Function.update] <;>
    (funext k; cases k <;> simp [stk, Function.update]))

private theorem countEnd (c : Bits) :
    step (cfg .count [] c [] [] [] []) = some (cfg .seedTag [] c [] [] [] []) := by
  (simp [cfg, done, stk, program, pop, push, jump, emitBit, Function.update] <;>
    (funext k; cases k <;> simp [stk, Function.update]))

private def countRun (w c : Bits) :
    let p := readCount w
    Run (cfg .count w c [] [] [] [])
      (cfg .seedTag p.2 (List.replicate p.1 true ++ c) [] [] [] []) (p.1 + 1) := by
  induction w generalizing c with
  | nil => exact one (countEnd c)
  | cons b w ih =>
    cases b with
    | false => exact one (countFalse w c)
    | true =>
      have hr (n : ℕ) : List.replicate n true ++ true :: c =
          List.replicate (n+1) true ++ c := by rw [List.replicate_add]; simp [List.append_assoc]
      simpa only [readCount, hr, Nat.add_comm 1 ((readCount w).1 + 1)] using
        seq (one (countTrue w c)) (ih (true :: c))

private theorem seedTagTrue (w c x : Bits) :
    step (cfg .seedTag (true :: w) c x [] [] []) = some (cfg .seedBit w c x [] [] []) := by
  (simp [cfg, done, stk, program, pop, push, jump, emitBit, Function.update] <;>
    (funext k; cases k <;> simp [stk, Function.update]))

private theorem seedTagFalse (w c x : Bits) :
    step (cfg .seedTag (false :: w) c x [] [] []) = some (cfg .nextRow w c x [] [] []) := by
  (simp [cfg, done, stk, program, pop, push, jump, emitBit, Function.update] <;>
    (funext k; cases k <;> simp [stk, Function.update]))

private theorem seedTagEnd (c x : Bits) :
    step (cfg .seedTag [] c x [] [] []) = some (cfg .nextRow [] c x [] [] []) := by
  (simp [cfg, done, stk, program, pop, push, jump, emitBit, Function.update] <;>
    (funext k; cases k <;> simp [stk, Function.update]))

private theorem seedValue (b : Bool) (w c x : Bits) :
    step (cfg .seedBit (b :: w) c x [] [] []) = some (cfg .seedTag w c (b :: x) [] [] []) := by
  cases b <;> (simp [cfg, done, stk, program, pop, push, jump, emitBit, Function.update] <;>
    (funext k; cases k <;> simp [stk, Function.update]))

private theorem seedValueEnd (c x : Bits) :
    step (cfg .seedBit [] c x [] [] []) = some (cfg .nextRow [] c x [] [] []) := by
  (simp [cfg, done, stk, program, pop, push, jump, emitBit, Function.update] <;>
    (funext k; cases k <;> simp [stk, Function.update]))

private def seedRun (w c x : Bits) :
    let p := readSeed w
    Run (cfg .seedTag w c x [] [] [])
      (cfg .nextRow p.2 c (p.1 ++ x) [] [] []) (2 * p.1.length + 2) := by
  induction w using List.twoStepInduction generalizing x with
  | nil => exact relax (one (seedTagEnd c x)) (by decide)
  | singleton b =>
    cases b with
    | false => exact relax (one (seedTagFalse [] c x)) (by decide)
    | true =>
      change Run (cfg .seedTag [true] c x [] [] []) (cfg .nextRow [] c x [] [] []) (1 + 1)
      exact seq (one (seedTagTrue [] c x)) (one (seedValueEnd c x))
  | cons_cons a b xs ih _ =>
    cases a with
    | false =>
      change Run (cfg .seedTag (false :: b :: xs) c x [] [] [])
        (cfg .nextRow (b :: xs) c x [] [] []) 2
      exact relax (one (seedTagFalse (b :: xs) c x)) (by decide)
    | true =>
      have h := seq (seq (one (seedTagTrue (b :: xs) c x)) (one (seedValue b xs c x))) (ih (b :: x))
      have ht : 2 * ((readSeed xs).1 ++ [b]).length + 2 = 1+1+(2*(readSeed xs).1.length+2) := by
        simp only [List.length_append, List.length_singleton]; omega
      simpa only [readSeed, ht, List.append_assoc, List.singleton_append] using h

private theorem startRow (r c x rev : Bits) :
    step (cfg .nextRow r (true :: c) x [] rev []) =
      some (cfg .row r.tail c x [] (r.headD false :: true :: rev) []) := by
  cases r with
  | nil => (simp [cfg, done, stk, program, pop, push, jump, emitBit, Function.update] <;>
    (funext k; cases k <;> simp [stk, Function.update]))
  | cons b r => cases b <;> (simp [cfg, done, stk, program, pop, push, jump, emitBit, Function.update] <;>
    (funext k; cases k <;> simp [stk, Function.update]))

private theorem endRows (r x rev : Bits) :
    step (cfg .nextRow r [] x [] rev []) = some (cfg .clearInput r [] x [] rev []) := by
  (simp [cfg, done, stk, program, pop, push, jump, emitBit, Function.update] <;>
    (funext k; cases k <;> simp [stk, Function.update]))

private theorem pairStep (b : Bool) (r c x s rev : Bits) :
    step (cfg .row r c (b :: x) s rev []) =
      some (cfg .row r.tail c x (b :: s) (b :: true :: r.headD false :: true :: rev) []) := by
  cases r with
  | nil => cases b <;> (simp [cfg, done, stk, program, pop, push, jump, emitBit, Function.update] <;>
    (funext k; cases k <;> simp [stk, Function.update]))
  | cons c₀ r => cases b <;> cases c₀ <;> (simp [cfg, done, stk, program, pop, push, jump, emitBit, Function.update] <;>
    (funext k; cases k <;> simp [stk, Function.update]))

private theorem endPairs (r c s rev : Bits) :
    step (cfg .row r c [] s rev []) = some (cfg .restore r c [] s (false :: rev) []) := by
  (simp [cfg, done, stk, program, pop, push, jump, emitBit, Function.update] <;>
    (funext k; cases k <;> simp [stk, Function.update]))

private theorem drop_succ (w : Bits) (n : ℕ) : w.drop (n + 1) = w.tail.drop n := by
  cases w <;> simp

private def pairRun (r c x s rev : Bits) :
    Run (cfg .row r c x s rev [])
      (cfg .restore (r.drop x.length) c [] (x.reverse ++ s)
        (false :: ((quoteBits (rowData x r)).reverse ++ rev)) []) (x.length+1) := by
  induction x generalizing r s rev with
  | nil => exact one (endPairs r c s rev)
  | cons b x ih =>
    simpa only [rowData, quoteBits, List.flatMap_cons, List.cons_append, List.nil_append,
      List.reverse_cons, List.append_assoc, List.singleton_append, List.length_cons, drop_succ,
      Nat.add_comm 1 (x.length + 1)] using
      seq (one (pairStep b r c x s rev)) (ih r.tail (b :: s) (b :: true :: r.headD false :: true :: rev))

private theorem restoreStep (b : Bool) (r c x s rev : Bits) :
    step (cfg .restore r c x (b :: s) rev []) =
      some (cfg .restore r c (b :: x) s rev []) := by
  cases b <;> (simp [cfg, done, stk, program, pop, push, jump, emitBit, Function.update] <;>
    (funext k; cases k <;> simp [stk, Function.update]))

private theorem restoreEnd (r c x rev : Bits) :
    step (cfg .restore r c x [] rev []) = some (cfg .nextRow r c x [] rev []) := by
  (simp [cfg, done, stk, program, pop, push, jump, emitBit, Function.update] <;>
    (funext k; cases k <;> simp [stk, Function.update]))

private def restoreRun (r c x s rev : Bits) :
    Run (cfg .restore r c x s rev [])
      (cfg .nextRow r c (s.reverse ++ x) [] rev []) (s.length+1) := by
  induction s generalizing x with
  | nil => exact one (restoreEnd r c x rev)
  | cons b s ih =>
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append, List.length_cons,
      Nat.add_comm 1 (s.length + 1)] using seq (one (restoreStep b r c x s rev)) (ih (b :: x))

private def rowsRun (r x rev : Bits) (j : ℕ) :
    Run (cfg .nextRow r (List.replicate j true) x [] rev [])
      (cfg .clearInput (r.drop (j * (x.length + 1))) [] x [] ((formatted x j r).reverse ++ rev) [])
      (j * (2*x.length + 3) + 1) := by
  induction j generalizing r rev with
  | zero =>
    simpa only [Nat.zero_mul, Nat.zero_add, List.drop_zero, formatted, rows, encodeWords,
      List.flatMap_nil, List.reverse_nil, List.nil_append, List.replicate_zero] using one (endRows r x rev)
  | succ j ih =>
    let c := List.replicate j true
    let suf := false :: ((quoteBits (rowData x r.tail)).reverse ++ (r.headD false :: true :: rev))
    have hPair := pairRun r.tail c x [] (r.headD false :: true :: rev)
    have hRestore :
        Run (cfg .restore (r.drop (x.length + 1)) c [] x.reverse suf [])
          (cfg .nextRow (r.drop (x.length + 1)) c x [] suf []) (x.length+1) := by
      simpa only [List.length_reverse, List.reverse_reverse, List.append_nil, drop_succ] using
        restoreRun (r.drop (x.length + 1)) c [] x.reverse suf
    have hp :
        Run (cfg .row r.tail c x [] (r.headD false :: true :: rev) [])
          (cfg .restore (r.drop (x.length + 1)) c [] x.reverse suf []) (x.length+1) := by
      simpa only [List.append_nil, drop_succ, suf] using hPair
    have h := seq (seq (seq (one (startRow r c x rev)) hp) hRestore) (ih (r.drop (x.length + 1)) suf)
    have hTime : 1 + (x.length+1) + (x.length+1) + (j*(2*x.length+3)+1) =
        (j+1)*(2*x.length+3)+1 := by rw [Nat.add_mul, Nat.one_mul]; omega
    have hNext : (x.length + 1) + j * (x.length + 1) = (j+1)*(x.length+1) := by
      rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
    simpa only [c, suf, List.replicate_succ, List.drop_drop, hNext, hTime,
      formatted, rows, encodeWords, List.flatMap_cons, List.reverse_append, quoteBits,
      List.cons_append, List.nil_append, List.reverse_cons, List.reverse_singleton,
      List.append_assoc, List.singleton_append] using h

private theorem clearInputStep (b : Bool) (r x rev : Bits) :
    step (cfg .clearInput (b :: r) [] x [] rev []) =
      some (cfg .clearInput r [] x [] rev []) := by
  cases b <;> (simp [cfg, done, stk, program, pop, push, jump, emitBit, Function.update] <;>
    (funext k; cases k <;> simp [stk, Function.update]))

private theorem clearInputEnd (x rev : Bits) :
    step (cfg .clearInput [] [] x [] rev []) = some (cfg .clearSeed [] [] x [] rev []) := by
  (simp [cfg, done, stk, program, pop, push, jump, emitBit, Function.update] <;>
    (funext k; cases k <;> simp [stk, Function.update]))

private def clearInputRun (r x rev : Bits) :
    Run (cfg .clearInput r [] x [] rev []) (cfg .clearSeed [] [] x [] rev []) (r.length+1) := by
  induction r with
  | nil => exact one (clearInputEnd x rev)
  | cons b r ih =>
    simpa only [List.length_cons, Nat.add_comm 1 (r.length + 1)] using
      seq (one (clearInputStep b r x rev)) ih

private theorem clearSeedStep (b : Bool) (x rev : Bits) :
    step (cfg .clearSeed [] [] (b :: x) [] rev []) = some (cfg .clearSeed [] [] x [] rev []) := by
  cases b <;> (simp [cfg, done, stk, program, pop, push, jump, emitBit, Function.update] <;>
    (funext k; cases k <;> simp [stk, Function.update]))

private theorem clearSeedEnd (rev : Bits) :
    step (cfg .clearSeed [] [] [] [] rev []) = some (cfg .emit [] [] [] [] rev []) := by
  (simp [cfg, done, stk, program, pop, push, jump, emitBit, Function.update] <;>
    (funext k; cases k <;> simp [stk, Function.update]))

private def clearSeedRun (x rev : Bits) :
    Run (cfg .clearSeed [] [] x [] rev []) (cfg .emit [] [] [] [] rev []) (x.length+1) := by
  induction x with
  | nil => exact one (clearSeedEnd rev)
  | cons b x ih =>
    simpa only [List.length_cons, Nat.add_comm 1 (x.length + 1)] using
      seq (one (clearSeedStep b x rev)) ih

private theorem emitStep (b : Bool) (rev out : Bits) :
    step (cfg .emit [] [] [] [] (b :: rev) out) = some (cfg .emit [] [] [] [] rev (b :: out)) := by
  cases b <;> (simp [cfg, done, stk, program, pop, push, jump, emitBit, Function.update] <;>
    (funext k; cases k <;> simp [stk, Function.update]))

private theorem emitEnd (out : Bits) :
    step (cfg .emit [] [] [] [] [] out) = some (done out) := by
  (simp [cfg, done, stk, program, pop, push, jump, emitBit, Function.update] <;>
    (funext k; cases k <;> simp [stk, Function.update]))

private def emitRun (rev out : Bits) :
    Run (cfg .emit [] [] [] [] rev out) (done (rev.reverse ++ out)) (rev.length+1) := by
  induction rev generalizing out with
  | nil => exact one (emitEnd out)
  | cons b rev ih =>
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append, List.length_cons,
      Nat.add_comm 1 (rev.length + 1)] using seq (one (emitStep b rev out)) (ih (b :: out))

private theorem rowData_length (x r : Bits) : (rowData x r).length = 2 * x.length := by
  induction x generalizing r with
  | nil => rfl
  | cons b xs ih => simp only [rowData, List.length_cons, ih]; omega

private theorem quoteBits_length (x : Bits) : (quoteBits x).length = 2 * x.length := by
  induction x with
  | nil => rfl
  | cons b xs ih =>
    change (true :: b :: quoteBits xs).length = _
    simp only [List.length_cons, ih]
    omega

private theorem formatted_length (x r : Bits) (j : ℕ) :
    (formatted x j r).length = j * (4*x.length+3) := by
  induction j generalizing r with
  | zero => simp [formatted, rows, encodeWords]
  | succ j ih =>
    change ((quoteBits (r.headD false :: rowData x r.tail) ++ [false]) ++
      formatted x j (r.drop (x.length+1))).length = _
    simp only [List.length_append, List.length_singleton, quoteBits_length, List.length_cons,
      rowData_length, ih, Nat.add_mul, Nat.one_mul, List.length_nil]
    omega

private def formatRun (w : Bits) :
    Run (cfg .count w [] [] [] [] []) (done (format w))
      ((w.length+1)*(10*w.length+10)) := by
  let p := readCount w
  let q := readSeed p.2
  let x := q.1
  let r := q.2
  let rest := r.drop (p.1 * (x.length+1))
  let rev := (formatted x p.1 r).reverse
  have h1 : Run (cfg .count w [] [] [] [] [])
      (cfg .seedTag p.2 (List.replicate p.1 true) [] [] [] []) (p.1+1) := by
    simpa only [List.append_nil] using countRun w []
  have h2 : Run (cfg .seedTag p.2 (List.replicate p.1 true) [] [] [] [])
      (cfg .nextRow r (List.replicate p.1 true) x [] [] []) (2*x.length+2) := by
    simpa only [List.append_nil] using seedRun p.2 (List.replicate p.1 true) []
  have h3 : Run (cfg .nextRow r (List.replicate p.1 true) x [] [] [])
      (cfg .clearInput rest [] x [] rev []) (p.1*(2*x.length+3)+1) := by
    simpa only [List.append_nil] using rowsRun r x [] p.1
  have h6 : Run (cfg .emit [] [] [] [] rev []) (done (format w))
      (p.1*(4*x.length+3)+1) := by
    simpa only [rev, format, p, q, x, r, List.reverse_reverse, List.append_nil,
      List.length_reverse, formatted_length] using emitRun rev []
  have hp : p.1 + p.2.length ≤ w.length := readCount_size w
  have hq : 2*x.length + r.length ≤ p.2.length := readSeed_size p.2
  have hRest : rest.length ≤ r.length := by simp [rest]
  have hRowCost : p.1*(2*x.length+3) ≤ w.length*(2*w.length+3) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hOutCost : p.1*(4*x.length+3) ≤ w.length*(4*w.length+3) :=
    Nat.mul_le_mul (by omega) (by omega)
  exact relax (seq (seq (seq (seq (seq h1 h2) h3) (clearInputRun rest x rev))
    (clearSeedRun x rev)) h6) (by nlinarith)

private theorem cfg_eq {c d : Cfg} (hl : c.l = d.l) (hv : c.var = d.var)
    (hs : ∀ t, c.stk t = d.stk t) : c = d := by
  have he := funext hs
  cases c
  cases d
  cases hl
  cases hv
  cases he
  rfl

private theorem init_eq (w : Bits) : initList machine w = cfg .count w [] [] [] [] [] := by
  refine cfg_eq (c := initList machine w) (d := cfg .count w [] [] [] [] []) rfl rfl ?_
  intro t
  cases t <;> simp [machine, initList, cfg, stk]

private theorem halt_eq (w : Bits) : haltList machine w = done w := by
  refine cfg_eq (c := haltList machine w) (d := done w) rfl rfl ?_
  intro t
  cases t <;> simp [machine, haltList, done, stk]

/-- Frame the affine row inputs while copying the shared seed once per row. -/
theorem format_polytime : PolyTimeComputable format := by
  let p : Polynomial ℕ :=
    (Polynomial.X + 1) * (Polynomial.C 10 * Polynomial.X + Polynomial.C 10)
  refine ⟨{
    tm := machine
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Equiv.refl Bool
    time := p
    outputsFun := ?_ }⟩
  intro w
  change Run (initList machine (w.map id)) (haltList machine ((format w).map id))
    (p.eval w.length)
  simpa only [List.map_id, init_eq, halt_eq, p, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_C] using formatRun w

private theorem rowData_eq_interleave (x r : Bits) (h : x.length ≤ r.length) :
    rowData x r = RowParityMachine.interleave (r.take x.length) x := by
  induction x generalizing r with
  | nil => rfl
  | cons b x ih =>
    cases r with
    | nil => simp at h
    | cons c r =>
      have hr : x.length ≤ r.length := by simpa only [List.length_cons, Nat.add_le_add_iff_right] using h
      change c :: b :: rowData x r = c :: b :: RowParityMachine.interleave (r.take x.length) x
      rw [ih r hr]

private theorem affinePrefix_succ (N j : ℕ) (r x : Bits) :
    ConstructionContracts.affinePrefix N (j+1) r x =
      Bool.xor (r.headD false) (ip (r.tail.take N) (x.take N)) ::
        ConstructionContracts.affinePrefix N j (r.drop (N+1)) x := by
  simp only [ConstructionContracts.affinePrefix, List.range_succ_eq_map, List.map_cons,
    Nat.zero_mul, Nat.zero_add, List.headD_eq_getD, List.drop_one, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  have hi : i.succ * (N+1) = (N+1) + i*(N+1) := by
    rw [Nat.succ_eq_add_one, Nat.add_mul, Nat.one_mul, Nat.add_comm]
  simp only [Function.comp_apply, hi, List.getD_eq_getElem?_getD, List.getElem?_drop,
    List.drop_drop, Nat.add_assoc]

private theorem rows_evaluate (x r : Bits) (j : ℕ) (hr : j*(x.length+1) ≤ r.length) :
    ((rows x j r).map RowParityMachine.evaluate).flatten =
      ConstructionContracts.affinePrefix x.length j r x := by
  induction j generalizing r with
  | zero => rfl
  | succ j ih =>
    have hra : x.length ≤ r.tail.length := by
      rw [← List.drop_one, List.length_drop]
      rw [Nat.succ_mul] at hr
      omega
    have hrb : j*(x.length+1) ≤ (r.drop (x.length+1)).length := by
      rw [List.length_drop]
      rw [Nat.succ_mul] at hr
      omega
    simp only [rows, List.map_cons, List.flatten_cons, rowData_eq_interleave _ _ hra,
      RowParityMachine.evaluate_affine_row, List.singleton_append, ih _ hrb,
      affinePrefix_succ, List.take_length]

theorem format_spec (j : ℕ) (x r : Bits) :
    format (enc j (quoteBits x.reverse ++ false :: r)) = encodeWords (rows x j r) := by
  simp only [format, readCount_spec, readSeed_spec, List.reverse_reverse, formatted]

theorem format_evaluates (j : ℕ) (x r : Bits) (hr : j*(x.length+1) ≤ r.length) :
    ∃ ws : List Bits,
      format (enc j (quoteBits x.reverse ++ false :: r)) = encodeWords ws ∧
      (ws.map RowParityMachine.evaluate).flatten =
        ConstructionContracts.affinePrefix x.length j r x :=
  ⟨rows x j r, format_spec j x r, rows_evaluate x r j hr⟩

end

end HILL.PRG.AffineRowsMachine

end HILL416_AffineRowsMachine

section HILL416_AffineEvaluator

set_option backward.isDefEq.respectTransparency.types false

namespace HILL.PRG

open WordCodecs ConstructionContracts MachineContracts
open CLRS.Chapter34.Turing.PolyBuilder

private theorem idPTimeParam : PTimeParam id := by
  refine ⟨⟨1, by decide, ?_⟩, ?_⟩
  · intro n hn
    have hn' : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr hn
    simp only [id_eq, Nat.cast_one, pow_one, one_mul]
    exact ⟨(div_le_one_of_le₀ hn' (zero_le_one.trans hn')).trans hn', le_rfl⟩
  · have h := polytime_unary_product (f := id) (g := fun _ => [true])
      polytime_idWord (polytime_constWord [true])
    simpa only [id_eq, List.length_cons, List.length_nil, Nat.zero_add, Nat.mul_one] using h

private def quoteBody : LoopBody Bool Bool where
  emit b := [true,b]
  cost _ := 2
  emit_length_le_cost _ := by simp

private theorem quoteBits_polytime : PolyTimeComputable quoteBits :=
  ⟨boundedLoop_computableInPolyTime quoteBody⟩

private theorem reverseWord_polytime : PolyTimeComputable (List.reverse : Bits → Bits) :=
  ⟨reverse_computableInPolyTime (Γ := Bool)⟩

set_option maxHeartbeats 1000000 in
/-- Evaluate the requested prefix of an affine map with a full-width key. -/
theorem affineEvaluator : AffineEvaluatorContract := by
  have hP : PTimeParam keyWidth := keyWidthPTime idPTimeParam
  obtain ⟨K, hK, hKey⟩ := payloadTake keyWidth hP
  let X := payloadDrop keyWidth
  have hX : PolyTimeComputable X := payloadDrop_polytime hP
  let J := (fun w => w ++ [false]) ∘ unaryParameter ∘ dropUnary
  have hJ : PolyTimeComputable J :=
    polytime_comp (polytime_comp dropUnary_polytime unaryParameter_polytime) polytime_append_false
  let quoted := (fun w => w ++ [false]) ∘ quoteBits ∘ List.reverse ∘ X
  have hQuoted : PolyTimeComputable quoted :=
    polytime_comp (polytime_comp (polytime_comp hX reverseWord_polytime) quoteBits_polytime)
      polytime_append_false
  let prepare (w : Bits) := J w ++ (quoted w ++ K w)
  have hPrepare : PolyTimeComputable prepare :=
    polytime_append hJ (polytime_append hQuoted hK)
  let frame (w : Bits) := [false, false] ++ (AffineRowsMachine.format ∘ prepare) w
  have hFrame : PolyTimeComputable frame :=
    polytime_append (polytime_constWord [false, false])
      (polytime_comp hPrepare AffineRowsMachine.format_polytime)
  let eval := RowParityMachine.evaluate ∘ splitAdviceHeader false
  have hEval : PolyTimeComputable eval :=
    polytime_comp (splitAdviceHeader_polytime false) RowParityMachine.evaluate_polytime
  obtain ⟨D, hD, hDWords⟩ := plainBatchCalls_of_batchCalls BatchMachine.batchCalls eval hEval
  refine ⟨D ∘ frame, polytime_comp hFrame hD, ?_⟩
  intro N j hj r hr x hx
  have hrl : r.length = keyWidth N := (HybridTape.mem_cube_length _ _).mp hr
  have hxl : x.length = N := (HybridTape.mem_cube_length _ _).mp hx
  let w := encAdvice N j (r ++ x)
  have hK' : K w = r := by
    have hsz : keyWidth N ≤ (r ++ x).length := by simp [← hrl]
    rw [show K w = (r ++ x).take (keyWidth N) from hKey N j (r ++ x) hsz, List.take_left' hrl]
  have hX' : X w = x := by
    rw [show X w = (r ++ x).drop (keyWidth N) from payloadDrop_encAdvice _ _ _ _, ← hrl,
      List.drop_left]
  have hJ' : J w = List.replicate j true ++ [false] := by
    simp only [J, Function.comp_apply, w, dropUnary_encAdvice, unaryParameter_replicate]
  have hQuote' : quoted w = quoteBits x.reverse ++ [false] := by
    simp only [quoted, Function.comp_apply, hX']
  have hPrep' : prepare w = enc j (quoteBits x.reverse ++ false :: r) := by
    simp [prepare, hK', hQuote', hJ', enc, List.append_assoc]
  have hRows : j*(x.length+1) ≤ r.length := by
    rw [hxl, hrl, keyWidth]
    exact Nat.mul_le_mul_right _ hj
  obtain ⟨ws, hws, hrow⟩ := AffineRowsMachine.format_evaluates j x r hRows
  have hFrame' : frame w = encAdvice 0 0 (encodeWords ws) := by
    simp only [frame, Function.comp_apply, hPrep', hws]
    rfl
  change D (frame w) = affinePrefix N j r x
  rw [hFrame', hDWords]
  have hmap : ws.map (fun x => eval (encAdvice 0 0 x)) = ws.map RowParityMachine.evaluate := by
    apply List.map_congr_left
    intro x _
    simp only [eval, Function.comp_apply, splitAdviceHeader_encAdvice, Bool.false_eq_true, if_false]
  rw [hmap, hrow, hxl]

end HILL.PRG

end HILL416_AffineEvaluator

open HILL.PRG

theorem solution :
    (∃ (F : FunEns) (a : ℕ → ℕ) (s : ℕ → ℝ), PolyParam s ∧ IsFalseEntropyGen F a s) →
      ∃ (G : FunEns) (b : ℕ → ℕ) (t : ℕ → ℝ), PolyParam t ∧ IsPseudoentropyGen G b t :=
  falseEntropyToPseudoentropy_of_affine_and_indist affineEvaluator constructionCompIndist
