-- Prove2me | solution 1 for HedgePSNV.stopped_integrand_representation
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-07T16:25:47.356298+00:00
-- url     : https://prove2.me/submissions/91ecbbd7-5b1a-47ad-a672-a9ecfaed075b

import Mathlib
import Definitions.Def_HedgePSNV_Hedging
import Definitions.Def_HedgePSNV_Model
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_completedBrownianPast
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral

set_option maxHeartbeats 2000000
set_option linter.all false
set_option Elab.async false

-- ===== slice of Solutions.Sol_pv_1558a108 (scratch/probe/slice8c/cuts/r_l2.lean.src/Solutions.Sol_pv_1558a108.lean): 0/153 top-level decls kept =====

set_option linter.all false
-- ===== ItoM1 =====

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

set_option autoImplicit false

namespace ItoLib
open EthierKurtz

variable {Ω : Type*} {d : ℕ}

section BM
variable [MeasurableSpace Ω]






end BM

section AEC
variable {mΩ : MeasurableSpace Ω}




end AEC

section CP
variable [MeasurableSpace Ω]



end CP

section M2


variable [MeasurableSpace Ω]






end M2

section M3
variable [MeasurableSpace Ω]





end M3

section M4
variable [MeasurableSpace Ω]


end M4


section StopCoef






end StopCoef

section M5
variable [MeasurableSpace Ω]




end M5


section M5b












end M5b

section M5c
variable [MeasurableSpace Ω]


end M5c


section M6refine



end M6refine


section M6osc










end M6osc


section M6cauchy
variable [MeasurableSpace Ω]


end M6cauchy


section M6limit
variable [MeasurableSpace Ω]



end M6limit


section M6trunc

















end M6trunc

section M6exist
variable [MeasurableSpace Ω]




end M6exist


section M7grid







end M7grid

section M7zero
variable [MeasurableSpace Ω]



end M7zero


section M7qv
variable [MeasurableSpace Ω]











end M7qv

section M7c
variable [MeasurableSpace Ω]



end M7c

section M8a
variable [MeasurableSpace Ω]








end M8a

section M8b
variable [MeasurableSpace Ω]


end M8b

section M8c
variable [MeasurableSpace Ω]



end M8c

section M8d
variable [MeasurableSpace Ω]




end M8d

section M8e
variable [MeasurableSpace Ω]






end M8e


section M8f
variable [MeasurableSpace Ω]


end M8f


section M8f2
variable [MeasurableSpace Ω]







end M8f2


section M8f3
variable [MeasurableSpace Ω]







end M8f3


section M8gTaylor
open Set



end M8gTaylor

section M8g
variable [MeasurableSpace Ω]



end M8g


section M8g2







end M8g2


section M8g3
variable [MeasurableSpace Ω]








end M8g3

section M8g4
variable [MeasurableSpace Ω]





end M8g4

section M8g5
variable [MeasurableSpace Ω]





end M8g5

section M9a
variable [MeasurableSpace Ω]




end M9a


section M9c
/-! M9c: calculus for the pathwise-uniqueness test function (line derivatives, cutoff). -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end M9c

section M9cF
/-! The concrete test function on `SDEState (d + d + 1)` = (x, y, a). -/

end M9cF


section M9c2
/-! Packing `(x, y, a)` into `SDEState (d + d + 1)` and the structure of `Ff`. -/

end M9c2


section M9d
/-! The generator of `Ff` along the coupled pair (x, y, a) and its sign inside the ball. -/

end M9d


section M9d2
/-! Global bounds for the generator and the integrands (compact support of `Ff` in (x, y)). -/

end M9d2



section M9e1
/-! Zero integral, measurability of time integrals, the exponential primitive identity, and the
pointwise generator bound with the localizing rate `kap`. -/

end M9e1


section M9e2
/-! Ito formula for `Ff r (X, Y, A)` and pathwise uniqueness for time-homogeneous, locally
Lipschitz coefficients (no stopping times: localization through the rate `kap`). -/

end M9e2


end ItoLib


-- ===== slice of P8c066573M16 (scratch/probe/slice8c/cuts/r_l2.lean.src/P8c066573M16.lean): 49/865 top-level decls kept =====

/-! Bridge from the HedgePSNV model to the ItoLib library (Solutions/Sol_pv_1558a108.lean):
a standard 2-d Brownian motion `W = (B, B~)` (modified on a null set so that every path is
continuous), with `F t ≤ completedBrownianPast P W 0 t`, and the transfer of
`HasBrownianItoIntegral` from `(F, B)` / `(F, B~)` to `(cBP, W · · 0)` / `(cBP, W · · 1)`. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace StochCalcBr

open HedgePSNV EthierKurtz

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]



































end StochCalcBr

/-! D1a (pathwise half): if an Ito integral `I` equals `-(1/2) ∫_0^· g` at all dyadic grid points
(`g = η²` continuous) and its quadratic-variation sums converge in measure to `∫_0^T g`
(ItoLib.qvJ_tendsto with `B := 1`, `H1 = H2 = η`), then `∫_0^T g = 0` a.s.
The QV sums of a continuous finite-variation path vanish: `∑ (∫_cell g)^2 ≤ M^2 T^2 / 2^n`. -/

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped NNReal ENNReal BigOperators

namespace StochCalcD1a

variable {Ω : Type*} [MeasurableSpace Ω]






end StochCalcD1a

/-! D1a wiring (relay 6): in the degenerate case `Z_T = 1` a.s., the drift `μ` vanishes
`dt`-a.e. on `[0,T]`, so `X_t = x₀ + J_t` for `t ≤ T`. The quadratic-variation input is the
hypothesis `hQV` = statement of the planned platform child C_QV (ItoLib.qvJ_tendsto with
`B := 1`, `j = j'`, `H1 = H2`). -/

namespace StochCalcD1aW

open HedgePSNV EthierKurtz StochCalcBr

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]










end StochCalcD1aW

/-! LA / D1b (relay 6 start): an Ito integral `J = ∫ H dW^j` of a continuous adapted integrand with
`E ∫_0^T H² < ∞` (and a.s. continuous paths on `[0,T]`) is square integrable and satisfies the
martingale property in set-integral form for every `A ∈ completedBrownianPast s`, `A` measurable.
(`completedBrownianPast` contains non-measurable null subsets, so `condExp` wrt it is junk;
the model side converts the set-integral form into `IsMartingaleOn` for `F`.)
Dev file: imports the accepted ItoLib (Sol_pv_1558a108); the platform child pastes the prefix. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter EthierKurtz
open scoped NNReal ENNReal Topology BigOperators

namespace StochCalcL2M

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}










/-! Lemma B (relay 7): martingale property of the Ito integral of a BOUNDED continuous adapted
integrand at dyadic grid times, set-integral form. -/





/-! Lemma C (relay 7): unbounded continuous adapted integrands with `E ∫_0^t H² < ∞`. -/






/-! Lemma D (relay 7): `L²` bound and martingale property at arbitrary times `s ≤ t`. -/



end StochCalcL2M

/-! D1b (relay 7): the model's `dB`-integral `J = ∫ Xσ dB` is a `P`-martingale on `[0,T]` (set-integral
form for `F`), and in the degenerate case `Z_T = 1` the price `X` is a `P`-martingale on `[0,T]`. -/

namespace StochCalcD1b

open HedgePSNV EthierKurtz StochCalcBr StochCalcL2M ItoLib

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]












end StochCalcD1b

/-! P1 for D2 (relay 7): the future increments of one Brownian coordinate `j` after `t₀` are
independent of the joint family {all coordinates up to `t₀`} ∪ {the other coordinates at all
times}. Used for the exponential tilts `Q_λ ∈ M_X` (D2) and Gaussian integration by parts. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter EthierKurtz
open scoped NNReal ENNReal Topology

namespace StochCalcIndep

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}




end StochCalcIndep

/-! P1b (relay 7): the model σ-algebras `F_c ⊔ G_T'` sit inside the a.e. closure of the
past-of-`B~`/all-of-`B` σ-algebra of the library Brownian motion `W M`; hence the `B~`
increments after `c` are independent of `F_c ⊔ G_T'`. -/

namespace StochCalcHs

open HedgePSNV EthierKurtz StochCalcBr StochCalcIndep ItoLib

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]








end StochCalcHs

/-! P2 for D2 (relay 8): Gaussian facts for a centred Gaussian `ξ ~ N(0, v)`:
exponential moments, the tilt `L c = exp(c ξ - v c²/2)` (mean one, in L²), and the
derivative-at-zero limit `E[ξ Y] = 0` from `E[(L c - 1) Y] = 0` for small `c ≠ 0` (DCT). -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace StochCalcGauss

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ξ : Ω → ℝ} {v : ℝ≥0}


















end StochCalcGauss

/-! P3 generic part (relay 8): change of measure by a positive mean-one L² density `D`,
set integrals / integrability under `Q = P.withDensity (ofReal ∘ D)`, the martingale property
under `Q` from set-integral identities under `P`, and the one-step tilt identity
`∫_A E R X_v = ∫_A E R X_s` (E `𝓕`-measurable, R independent of `𝓗 ⊇ 𝓕`, mean one). -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace StochCalcTilt

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]












end StochCalcTilt
/-! P3 model part (relay 8): the exponential `B~`-increment tilts
`Q_c = P.withDensity (exp(c (B~_{t'} - B~_t) - c²(t'-t)/2))` belong to `M_X` whenever `X` is an
L² `P`-martingale on `[0, T]` (degenerate case). -/

namespace StochCalcTiltM

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]



















end StochCalcTiltM
/-! P4 (relay 8): every admissible gains process is orthogonal to the future `B~` increments:
`E[Y ξ χ_T] = 0` for `ξ = B~_{t'} - B~_t` and bounded `F_t`-measurable `Y` (degenerate case,
`X` an L² `P`-martingale), via the tilts `Q_c ∈ M_X` and `d/dc|₀`. -/

namespace StochCalcOrth

open HedgePSNV EthierKurtz StochCalcBr StochCalcGauss StochCalcTilt StochCalcTiltM

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]





end StochCalcOrth

/-! P5 for D2 (relay 9): Gaussian integration by parts (Stein) for the hinge
`x ↦ max (k - s x) 0`, and its independent-conditioning form
`E[ξ (k0 - a (R - (U + s ξ))^+) Y] = a s v E[Y 1{U + s ξ ≤ R}]` for `ξ ~ N(0, v)` independent of `(U, Y)`. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace StochCalcStein








end StochCalcStein
/-! P5 model part (relay 9): Stein identity for the production payoff against a `B~` increment:
`E[ξ H Y] = (P - s) σ~ (t' - t) E[Y 1{A_T ≤ R}]` for `ξ = B~_{t'} - B~_t` and bounded `F_t`-measurable `Y`
(no degeneracy needed: `ξ` is independent of `F_t ⊔ G_T ⊔ σ(B~_T - B~_{t'})`). -/

namespace StochCalcSteinM

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcTiltM StochCalcStein

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]






end StochCalcSteinM

/-! P6 generic pieces (relay 9): (A) a variance lower bound from a test variable `D` with
`E D = 0` and `E[D U] = E[D²]`; (B) left Riemann sums of a monotone function on a uniform grid. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace StochCalcP6




/-! P6 generic (relay 10): martingale-difference sums `S n = Σ_{k<n} Y k * ξ k` with `ξ k`
independent of `m k`, centred, in `L²`, `m (k+1)`-measurable, and `Y k` bounded `m k`-measurable:
`E S = 0`, `S ∈ L²`, `E S² = Σ E[Y k²] E[ξ k²]`. Plus Gaussian moments. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace StochCalcP6S

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]




variable (m : ℕ → MeasurableSpace Ω) (ξ Y : ℕ → Ω → ℝ)



end StochCalcP6S

/-! Degenerate case `Z_T = 1` a.s. of Theorem 1(ii) (child `HedgePSNV.theorem_1_ii_degenerate` of
proposition_5 cc6d45ce): reduction of the child to three stochastic obligations
  (D1) `X` is a `P`-martingale on `[0,T]`,
  (D2) lower bound `Psi ≤ Var[H + χ_T]` for every admissible strategy,
  (D3) approximate attainment `∃ (θ,χ) ∈ A_X, Var[H + χ_T] ≤ Psi + ε`,
plus the elementary degenerate facts (`P^M = P`, `Z_t = Z^M_t = 1` a.s., `E χ_T = 0`). -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace StochCalcHedgeDeg

open HedgePSNV

variable {p : Params} {Ω : Type*} [MeasurableSpace Ω]











end StochCalcHedgeDeg

/-! D2 (relay 10): the degenerate lower bound `Psi ≤ Var[H + χ_T]` for every admissible strategy,
via the test variables `D_n = Σ_k σ~(P-s) c_{t_k} ξ_k` (P4 orthogonality, P5 Stein, P6 Riemann sums). -/

namespace StochCalcD2

open HedgePSNV StochCalcBr StochCalcTiltM StochCalcSteinM StochCalcOrth StochCalcHedgeDeg StochCalcGauss

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]




















end StochCalcD2

/-! D2 limit (relay 10): Riemann sums of the monotone `u ↦ E[δ_u²]` and `Psi_deg`. -/

namespace StochCalcD2

open HedgePSNV StochCalcBr StochCalcTiltM StochCalcHedgeDeg

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]









end StochCalcD2
/-! D3 reduction (relay 11): approximate attainment `Var[H + χ_T] ≤ Psi + ε` from ONE
L²-density statement (`hdens` of `StochCalcD3.D3_of_density`): for every `η > 0` some
admissible `χ`, constant `c` and simple `dB̃`-sum `K = Σ Z_k ξ_k` on a uniform grid have
`E[(H + χ_T − c − K)²] ≤ η`.  Proof: `D = Σ σ̃(P−s) Yc_{t_k} ξ_k` is the projection of
`U = H + χ_T − c` onto the simple `dB̃`-sums of the grid (Stein + polarized isometry), so
`E U² ≤ E D² + E (U − K)²`, and `E D²` is a left Riemann sum of the monotone `u ↦ E δ_u²`. -/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace StochCalcP6




end StochCalcP6

namespace StochCalcP6S

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable (m : ℕ → MeasurableSpace Ω) (ξ : ℕ → Ω → ℝ)


end StochCalcP6S

namespace StochCalcD3

open HedgePSNV StochCalcBr StochCalcTiltM StochCalcSteinM StochCalcOrth StochCalcHedgeDeg
  StochCalcGauss StochCalcD2

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]



end StochCalcD3
/-! D3 split (relay 11): `hdens` of `D3_of_density` from
  (R)  representation density: `H ≈ c + Σ Y_k ΔB_k + Σ Z_k ΔB̃_k` in L² on a uniform grid;
  (XS) hedging of a simple `dB`-sum by an admissible strategy: `χ_T ≈ −Σ Y_k ΔB_k` in L².
Grid refinement `n → n*m` is exact (telescoping). -/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace StochCalcD3

open HedgePSNV StochCalcBr StochCalcTiltM StochCalcSteinM StochCalcOrth StochCalcHedgeDeg
  StochCalcGauss StochCalcD2

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]








end StochCalcD3

/-! R1 generic (relay 13): telescoping-product approximation of `exp (i Σ x_k)` by a constant
plus an adapted "stochastic sum" `Σ A_k (i x_k)`, for a discrete filtration `m` and increments
`x k` that are `m (k+1)`-measurable, independent of `m k`, centred, with `E x_k⁴ ≤ D`.
Error in `L²`: `≤ 16 n D`.  Mathlib only. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Finset
open scoped NNReal ENNReal

namespace StochCalcR1



variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]









end StochCalcR1

/-! R1 model (relay 13): `exp (i Σ_k (λ_k ΔB_k + μ_k ΔB~_k))` on a uniform grid is `L²`-close to a
constant plus an adapted fine-grid sum `Σ_l A_l · i (a_l ΔB_l + b_l ΔB~_l)`.  Needs the joint
independence of `(ΔB, ΔB~)` on `[u, w]` from `F_u` (new: `indep_B_incr`, `indep_pair`). -/

namespace StochCalcR1M

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcIndep ItoLib StochCalcTiltM
  StochCalcSteinM StochCalcStein StochCalcD2 StochCalcD3 StochCalcGauss StochCalcP6S Finset

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]






















end StochCalcR1M

/-! R4 (relay 13): the class `IsGS` of grid sums `c + Σ Y_k ΔB_k + Σ Z_k ΔB~_k` (bounded adapted
coefficients on a uniform grid) is a vector space of `F_T`-measurable `L²` functions. -/

namespace StochCalcR4

open HedgePSNV StochCalcTiltM StochCalcD2 StochCalcD3 StochCalcGauss Finset

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]







end StochCalcR4

/-! R2a (relay 12): characteristic-function identification.  If an integrable `V` is orthogonal to
`cos ⟪Δ, t⟫` and `sin ⟪Δ, t⟫` for every `t`, then `∫_A V = 0` for every `A ∈ σ(Δ)`.
Mathlib only. -/

open MeasureTheory ProbabilityTheory Complex
open scoped ENNReal

namespace StochCalcR2

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E] [mE : MeasurableSpace E] [BorelSpace E]



end StochCalcR2

/-! R2b (relay 12): π-λ extension of vanishing set integrals from an increasing sequence of
σ-algebras to their supremum joined with the `P`-null sets, and the a.e.-limit criterion that
puts a variable's σ-algebra below it.  Mathlib only. -/

open MeasureTheory Filter
open scoped ENNReal Topology

namespace StochCalcR2








end StochCalcR2

/-! R2c (relay 12): the generic identification theorem. -/

namespace StochCalcR2

open MeasureTheory


end StochCalcR2

/-! R3 (relay 12): Hilbert-space glue.  A subspace (given as a predicate on functions) of `L²`
whose orthogonal complement is trivial is `L²`-dense.  Mathlib only. -/

open MeasureTheory Filter
open scoped ENNReal

namespace StochCalcR3


end StochCalcR3

/-! R6 generic (relay 13): orthogonality passes to `L²`-limits.  Mathlib only. -/

set_option autoImplicit false

open MeasureTheory

namespace StochCalcR6



end StochCalcR6

/-! R5 (relay 14): the grid-`2^j` increment vectors `Δ_j` of `(B, B~)`, the monotonicity of
their σ-algebras, `F_T ≤ aug (⨆ σ(Δ_j))`, and `⟪Δ_j, t⟫` as a grid sum. -/

namespace StochCalcR5

open HedgePSNV StochCalcTiltM StochCalcD2 StochCalcD3 StochCalcR4 StochCalcR2 Finset Filter
open scoped Topology



variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]





















end StochCalcR5

/-! R7 (relay 14): trigonometric functions of `Δ_j` are `L²`-limits of grid sums; hence the
grid sums are dense in `L²(F_T)` (hsep + R3), which is the hypothesis `hR` of `dens_of_rep`. -/

namespace StochCalcR7

open HedgePSNV StochCalcTiltM StochCalcD2 StochCalcD3 StochCalcR4 StochCalcR5 StochCalcR1M
  Finset Filter




variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]









end StochCalcR7

/-! TC (relay 15 of cc6d45ce): truncation consistency of the Ito integral at an ARBITRARY time
`r ≤ t`.  The clamped left-point sums of the horizon-`t` dyadic grid, masked to the cells that
start before `r`, converge in probability to `J r`, given that `J` is continuous in probability
along the dyadic floors `r_n ↑ r`.  Three-term argument: dyadic floor `r_n` (ItoLib M7a
`partialSum_tendsto_of_hasBrownianItoIntegral`), the cells in `[r_n, r)` (Lenglart bound
`itoStepSum_local_chebyshev`, at most `2^m` cells of length `t/2^(n+m)`), and `J r_n → J r`.
Use: hXS step S1 (Ito integral of a simple-in-time strategy times `Xσ`). -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter EthierKurtz
open scoped NNReal ENNReal Topology BigOperators

namespace StochCalcTC

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}
















/-! S1b preparation (relay 15): one cell for every coefficient family; `thetaS` bounds. -/





end StochCalcTC

/-! TC2 (relay 16 of cc6d45ce): S1b, the integrated-squared-error clause for the
`thetaS · clamp_N H` approximants. -/

namespace StochCalcTC

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]








end StochCalcTC

/-! TC3 (relay 16 of cc6d45ce): S1 assembly.  The Ito integral of the simple-in-time weight
`thetaS s θ n'` times a continuous adapted `H` is `Σ_i θ_i (J(s_{i+1} ∧ t) − J(s_i ∧ t))`. -/

namespace StochCalcTC

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}





end StochCalcTC

/-! TC4 (relay 16 of cc6d45ce): variant of S1c needing `J`-continuity only at the jump times;
dyadic floors converge; clause 1 of the Ito relation for `thetaS · H`. -/

namespace StochCalcTC

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}





end StochCalcTC

/-! Mart (relay 16 of cc6d45ce): simple stochastic integrals of a martingale are martingales.
`θ (X(b ∧ t) − X(a ∧ t))` with `θ` bounded `F a`-measurable is an `IsMartingaleOn` martingale;
finite sums too.  Generic (any filtration, any finite measure). -/

set_option autoImplicit false

open MeasureTheory Filter
open scoped NNReal

namespace StochCalcMart

open HedgePSNV

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]






end StochCalcMart

/-! S1M (relay 16 of cc6d45ce): in the degenerate model, a simple-in-time strategy
`thetaS s θ n'` (jump times `s_i ≤ T`, `θ_i` bounded `F(s_i)`-measurable) with gains
`chiS = Σ θ_i (X(s_{i+1} ∧ t) − X(s_i ∧ t))` is admissible: `(thetaS, chiS) ∈ A_X`. -/

namespace StochCalcS1M

open HedgePSNV EthierKurtz StochCalcBr StochCalcD1b StochCalcD1aW StochCalcTC StochCalcMart ItoLib

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]











end StochCalcS1M

/-! TCR (8c066573 relay 15, O2 core): truncation consistency at a RANDOM cutoff `ρ ≤ t` that is a
stopping time of the completed Brownian past.  Same three-term argument as `truncSum_tendsto`,
with the dyadic CEILING `ρ^n = dyTime t n ⌈ρ/t·2^n⌉` (a stopping time, finitely many values):
masked sums up to `ρ^n` are finitely many deterministic truncations (`trunc_dy_tendsto`), the
cells in `[ρ, ρ^n)` are adapted (Lenglart), and `J (ρ^n) → J ρ` is a hypothesis. -/

namespace StochCalcTC

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}











end StochCalcTC

/-! S1b with RANDOM jump times `s ω` (8c066573 relay 15): the argument is pathwise. -/

namespace StochCalcTC

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}



end StochCalcTC

/-! S1RM (8c066573 relay 15, O2b): the Ito relation for a STOPPED simple strategy
`θ = Y 1{s∧τ ≤ u < s'∧τ}` in the model, with `K_t = Y (J(s'∧τ∧t) − J(s∧τ∧t))`.
Append after probe/cc6d45ce_S1M.lean + lib/stochcalc/TCR_tail.lean + lib/stochcalc/S1bR_tail.lean.
Hypothesis `hJc` (J along dyadic ceilings of a random time) is discharged separately (needs s' < T). -/

namespace StochCalcS1R

open HedgePSNV EthierKurtz StochCalcBr StochCalcD1b StochCalcD1aW StochCalcTC StochCalcMart
  StochCalcS1M ItoLib

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]









end StochCalcS1R
/-! S1RJ (8c066573 relay 16, O2c): discharge `hJc` of `S1R_model` for random times bounded by
`s' < T`, giving `S1R_modelT` (no `hJc` hypothesis).
Append after probe/8c066573_S1R.lean (= cc6d45ce_S1M + TCR_tail + S1bR_tail + S1RM_tail). -/

namespace StochCalcS1R

open HedgePSNV EthierKurtz StochCalcBr StochCalcD1b StochCalcD1aW StochCalcTC StochCalcMart
  StochCalcS1M ItoLib

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]






end StochCalcS1R

/-! OS (8c066573 relay 14): continuous-time optional stopping for `IsMartingaleOn`.
A continuous martingale on `[0,T]` stopped at a stopping time is again a martingale on `[0,T]`.
Proof: grid stopping times `jn` on `s + k (t-s)/(N+1)` (Mathlib discrete optional sampling gives
`X(grid ceiling of ρ) = E[X t | F_ρN]`), uniform integrability of conditional expectations,
pointwise convergence by path continuity, Vitali.  Generic (any filtration, finite measure). -/

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace StochCalcOS

open HedgePSNV

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]



























end StochCalcOS

/-! Hit (8c066573 relay 16, O2a): the hitting time of the closed set `{R ≤ |x|}` by a process
with continuous paths, capped at `T`, is a stopping time of any filtration to which the
process is adapted (no right-continuity of the filtration needed: closed set + continuous paths).
Also: the stopped process is bounded by `R` when it starts inside. Mathlib only. -/

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace StochCalcHit

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]











end StochCalcHit
/-! S1RA (8c066573 relay 16, O2d): the stopped simple strategy
`θ = Y 1{s∧τ ≤ u < s'∧τ}`, `χ_t = Y (X_{s'∧τ∧t} − X_{s∧τ∧t})` is admissible (`∈ M.AX`) when
`s ≤ s' < T`, `τ` is a stopping time and the stopped price is bounded (e.g. `τ = hitR`).
Append after probe/8c066573_S1RJ.lean + the body of lib/stochcalc/Hit.lean (no import line). -/

namespace StochCalcS1R

open HedgePSNV EthierKurtz StochCalcBr StochCalcD1b StochCalcD1aW StochCalcTC StochCalcMart
  StochCalcS1M ItoLib StochCalcOS StochCalcHit

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]











end StochCalcS1R

/-! RieszIso (8c066573 relay 16, O3 core): if a linear map `T : S → F` into a Hilbert space is
isometric for a seminorm given by a linear map `e : S → E` into another Hilbert space
(`‖T s‖ = ‖e s‖`), then every `f ∈ F` has a "representing integrand" `a ∈ E` with
`⟪f, T s⟫ = ⟪a, e s⟫` for all `s`.  (Use: `S` = simple adapted processes, `e` = their class in
`L²(dt ⊗ dP)`, `T` = the elementary stochastic integral into `L²(P)`.)  Mathlib only; no quotient
by null processes is needed. -/

set_option autoImplicit false

open Filter Topology
open scoped InnerProductSpace RealInnerProductSpace

namespace StochCalcRiesz

variable {S E F : Type*} [AddCommGroup S] [Module ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]




end StochCalcRiesz

/-! O3gen (8c066573 relay 17, O3 instantiation, generic; append after RieszIso.lean, Mathlib only).
For a real process `W` with independent centred increments of variance `v - u` w.r.t. a monotone family
`m t` of σ-algebras, every `f ∈ L²(P)` has a representing integrand `a ∈ L²(dt|[0,T] ⊗ P)` (in the closure of
the adapted simple processes) with `E[f · Y (W_v - W_u)] = ∫∫ a · 1_[u,v) Y` for all bounded `m u`-measurable `Y`. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Increment hypotheses on a real process `W` w.r.t. a family of σ-algebras `m`. -/
structure IncrHyp (m : ℝ≥0 → MeasurableSpace Ω) (W : ℝ≥0 → Ω → ℝ) (P : Measure Ω) : Prop where
  mono : Monotone m
  le : ∀ t, m t ≤ mΩ
  adapt : ∀ t, Measurable[m t] (W t)
  indep : ∀ u v, u ≤ v →
    Indep (m u) (MeasurableSpace.comap (fun ω => W v ω - W u ω) inferInstance) P
  mem2 : ∀ u v, MemLp (fun ω => W v ω - W u ω) 2 P
  mean : ∀ u v, u ≤ v → ∫ ω, (W v ω - W u ω) ∂P = 0
  var : ∀ u v, u ≤ v → ∫ ω, (W v ω - W u ω) ^ 2 ∂P = (v : ℝ) - u

variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}

lemma dW_meas (hW : IncrHyp m W P) {u v : ℝ≥0} (huv : u ≤ v) :
    Measurable[m v] (fun ω => W v ω - W u ω) :=
  (hW.adapt v).sub ((hW.adapt u).mono (hW.mono huv) le_rfl)

lemma dW_measAmb (hW : IncrHyp m W P) (u v : ℝ≥0) : Measurable (fun ω => W v ω - W u ω) :=
  ((hW.adapt v).mono (hW.le v) le_rfl).sub ((hW.adapt u).mono (hW.le u) le_rfl)

lemma int_mul_dW (hW : IncrHyp m W P) {c d : ℝ≥0} (hcd : c ≤ d) {g : Ω → ℝ}
    (hg : Measurable[m c] g) : ∫ ω, g ω * (W d ω - W c ω) ∂P = 0 := by
  have hind : IndepFun g (fun ω => W d ω - W c ω) P := by
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le_left (hW.indep c d hcd) hg.comap_le
  rw [hind.integral_fun_mul_eq_mul_integral (hg.mono (hW.le c) le_rfl).aestronglyMeasurable
    (dW_measAmb hW c d).aestronglyMeasurable, hW.mean c d hcd, mul_zero]

lemma int_mul_dW_sq (hW : IncrHyp m W P) {c d : ℝ≥0} (hcd : c ≤ d) {g : Ω → ℝ}
    (hg : Measurable[m c] g) :
    ∫ ω, g ω * (W d ω - W c ω) ^ 2 ∂P = (∫ ω, g ω ∂P) * ((d : ℝ) - c) := by
  have hind : IndepFun g (fun ω => (W d ω - W c ω) ^ 2) P := by
    rw [IndepFun_iff_Indep]
    refine indep_of_indep_of_le_right
      (indep_of_indep_of_le_left (hW.indep c d hcd) hg.comap_le) ?_
    exact ((comap_measurable (fun ω => W d ω - W c ω)).pow_const 2).comap_le
  rw [hind.integral_fun_mul_eq_mul_integral (hg.mono (hW.le c) le_rfl).aestronglyMeasurable
    ((dW_measAmb hW c d).pow_const 2).aestronglyMeasurable, hW.var c d hcd]

lemma int_mul_dW_dW (hW : IncrHyp m W P) {c x y : ℝ≥0} (hcx : c ≤ x) (hxy : x ≤ y) {g : Ω → ℝ}
    (hg : Measurable[m c] g) {C : ℝ} (hC : ∀ ω, |g ω| ≤ C) :
    ∫ ω, g ω * ((W x ω - W c ω) * (W y ω - W c ω)) ∂P = (∫ ω, g ω ∂P) * ((x : ℝ) - c) := by
  have hga : AEStronglyMeasurable g P := (hg.mono (hW.le c) le_rfl).aestronglyMeasurable
  have hgb : ∀ᵐ ω ∂P, ‖g ω‖ ≤ C :=
    Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hC ω
  have i1 : Integrable (fun ω => g ω * (W x ω - W c ω) ^ 2) P :=
    (hW.mem2 c x).integrable_sq.bdd_mul hga hgb
  have i2 : Integrable (fun ω => g ω * ((W x ω - W c ω) * (W y ω - W x ω))) P :=
    ((hW.mem2 c x).integrable_mul (hW.mem2 x y)).bdd_mul hga hgb
  have i2' : Integrable (fun ω => g ω * (W x ω - W c ω) * (W y ω - W x ω)) P := by
    simpa only [mul_assoc] using i2
  have e : (fun ω => g ω * ((W x ω - W c ω) * (W y ω - W c ω))) =
      fun ω => g ω * (W x ω - W c ω) ^ 2 + g ω * (W x ω - W c ω) * (W y ω - W x ω) := by
    funext ω; ring
  have hg2 : Measurable[m x] (fun ω => g ω * (W x ω - W c ω)) :=
    (hg.mono (hW.mono hcx) le_rfl).mul (dW_meas hW hcx)
  rw [e, integral_add i1 i2', int_mul_dW_sq hW hcx hg, int_mul_dW hW hxy hg2, add_zero]

/-- Overlap length of `[u,v)` and `[u',v')`. -/
noncomputable def ov (u v u' v' : ℝ≥0) : ℝ := max (min (v : ℝ) v' - max (u : ℝ) u') 0

lemma ov_comm (u v u' v' : ℝ≥0) : ov u v u' v' = ov u' v' u v := by
  unfold ov; rw [min_comm, max_comm (u : ℝ)]

/-- Covariance of two elementary increments (case `u ≤ u'`). -/
lemma cov_le (hW : IncrHyp m W P) {u v u' v' : ℝ≥0} (huv : u ≤ v) (hu'v' : u' ≤ v')
    (huu' : u ≤ u') {Y Y' : Ω → ℝ} (hY : Measurable[m u] Y) (hY' : Measurable[m u'] Y')
    {C C' : ℝ} (hC : ∀ ω, |Y ω| ≤ C) (hC' : ∀ ω, |Y' ω| ≤ C') :
    ∫ ω, (Y ω * (W v ω - W u ω)) * (Y' ω * (W v' ω - W u' ω)) ∂P =
      (∫ ω, Y ω * Y' ω ∂P) * ov u v u' v' := by
  have hYu' : Measurable[m u'] Y := hY.mono (hW.mono huu') le_rfl
  have hYY' : Measurable[m u'] (fun ω => Y ω * Y' ω) := hYu'.mul hY'
  have hbd : ∀ ω, |Y ω * Y' ω| ≤ C * C' := fun ω => by
    rw [abs_mul]
    exact mul_le_mul (hC ω) (hC' ω) (abs_nonneg _) ((abs_nonneg _).trans (hC ω))
  have hu'r : (u : ℝ) ≤ u' := by exact_mod_cast huu'
  rcases le_or_gt v u' with hvu | hu'v
  · have hvu' : (v : ℝ) ≤ u' := by exact_mod_cast hvu
    have hov : ov u v u' v' = 0 := by
      unfold ov
      exact max_eq_right (by linarith [min_le_left (v : ℝ) v', le_max_right (u : ℝ) u'])
    have e : (fun ω => (Y ω * (W v ω - W u ω)) * (Y' ω * (W v' ω - W u' ω))) =
        fun ω => (Y ω * (W v ω - W u ω) * Y' ω) * (W v' ω - W u' ω) := by
      funext ω; ring
    have hg : Measurable[m u'] (fun ω => Y ω * (W v ω - W u ω) * Y' ω) :=
      (hYu'.mul ((dW_meas hW huv).mono (hW.mono hvu) le_rfl)).mul hY'
    rw [e, int_mul_dW hW hu'v' hg, hov, mul_zero]
  · have hu'v'' : (u' : ℝ) < v := by exact_mod_cast hu'v
    have hu'v1 : u' ≤ v := hu'v.le
    have hga : AEStronglyMeasurable (fun ω => Y ω * Y' ω) P :=
      (hYY'.mono (hW.le u') le_rfl).aestronglyMeasurable
    have hgb : ∀ᵐ ω ∂P, ‖Y ω * Y' ω‖ ≤ C * C' :=
      Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hbd ω
    have i1 : Integrable (fun ω => Y ω * Y' ω * ((W u' ω - W u ω) * (W v' ω - W u' ω))) P :=
      ((hW.mem2 u u').integrable_mul (hW.mem2 u' v')).bdd_mul hga hgb
    have i2 : Integrable (fun ω => Y ω * Y' ω * ((W v ω - W u' ω) * (W v' ω - W u' ω))) P :=
      ((hW.mem2 u' v).integrable_mul (hW.mem2 u' v')).bdd_mul hga hgb
    have i1' : Integrable (fun ω => Y ω * Y' ω * (W u' ω - W u ω) * (W v' ω - W u' ω)) P := by
      simpa only [mul_assoc] using i1
    have e : (fun ω => (Y ω * (W v ω - W u ω)) * (Y' ω * (W v' ω - W u' ω))) =
        fun ω => Y ω * Y' ω * (W u' ω - W u ω) * (W v' ω - W u' ω) +
          Y ω * Y' ω * ((W v ω - W u' ω) * (W v' ω - W u' ω)) := by
      funext ω; ring
    have hg1 : Measurable[m u'] (fun ω => Y ω * Y' ω * (W u' ω - W u ω)) :=
      hYY'.mul (dW_meas hW huu')
    rw [e, integral_add i1' i2, int_mul_dW hW hu'v' hg1, zero_add]
    rcases le_total v v' with hvv | hvv
    · rw [int_mul_dW_dW hW hu'v1 hvv hYY' hbd]
      congr 1
      unfold ov
      have hvv' : (v : ℝ) ≤ v' := by exact_mod_cast hvv
      rw [min_eq_left hvv', max_eq_right hu'r, max_eq_left (by linarith)]
    · have e2 : (fun ω => Y ω * Y' ω * ((W v ω - W u' ω) * (W v' ω - W u' ω))) =
          fun ω => Y ω * Y' ω * ((W v' ω - W u' ω) * (W v ω - W u' ω)) := by
        funext ω; ring
      rw [e2, int_mul_dW_dW hW hu'v' hvv hYY' hbd]
      congr 1
      unfold ov
      have hvv' : (v' : ℝ) ≤ v := by exact_mod_cast hvv
      have hu'v'r : (u' : ℝ) ≤ v' := by exact_mod_cast hu'v'
      rw [min_eq_right hvv', max_eq_right hu'r, max_eq_left (by linarith)]

lemma cov (hW : IncrHyp m W P) {u v u' v' : ℝ≥0} (huv : u ≤ v) (hu'v' : u' ≤ v')
    {Y Y' : Ω → ℝ} (hY : Measurable[m u] Y) (hY' : Measurable[m u'] Y')
    {C C' : ℝ} (hC : ∀ ω, |Y ω| ≤ C) (hC' : ∀ ω, |Y' ω| ≤ C') :
    ∫ ω, (Y ω * (W v ω - W u ω)) * (Y' ω * (W v' ω - W u' ω)) ∂P =
      (∫ ω, Y ω * Y' ω ∂P) * ov u v u' v' := by
  rcases le_total u u' with h | h
  · exact cov_le hW huv hu'v' h hY hY' hC hC'
  · have := cov_le hW hu'v' huv h hY' hY hC' hC
    have e1 : (fun ω => (Y ω * (W v ω - W u ω)) * (Y' ω * (W v' ω - W u' ω))) =
        fun ω => (Y' ω * (W v' ω - W u' ω)) * (Y ω * (W v ω - W u ω)) := by
      funext ω; ring
    have e2 : (fun ω => Y ω * Y' ω) = fun ω => Y' ω * Y ω := by funext ω; ring
    rw [e1, e2, this, ov_comm]

/-- Time indicator of `[u, v)`. -/
noncomputable def ind (u v : ℝ≥0) (r : ℝ) : ℝ := (Set.Ico (u : ℝ) v).indicator (fun _ => (1 : ℝ)) r

lemma ind_mul (u v u' v' : ℝ≥0) (r : ℝ) :
    ind u v r * ind u' v' r =
      (Set.Ico (max (u : ℝ) u') (min (v : ℝ) v')).indicator (fun _ => (1 : ℝ)) r := by
  simp only [ind, Set.indicator_apply, Set.mem_Ico, max_le_iff, lt_min_iff]
  split_ifs <;> simp_all

lemma ind_abs_le (u v : ℝ≥0) (r : ℝ) : |ind u v r| ≤ 1 := by
  unfold ind; rw [Set.indicator_apply]; split_ifs <;> simp

lemma ind_meas (u v : ℝ≥0) : Measurable (ind u v) :=
  (measurable_const.indicator measurableSet_Ico)

/-- The time-space measure `dt|[0,T) ⊗ P`. -/
noncomputable def μT (P : Measure Ω) (T : ℝ≥0) : Measure (ℝ × Ω) :=
  (volume.restrict (Set.Ico (0 : ℝ) T)).prod P

instance (T : ℝ≥0) : IsFiniteMeasure (μT P T) := by unfold μT; infer_instance

lemma int_time (T : ℝ≥0) {u v u' v' : ℝ≥0} (hvT : v ≤ T) :
    ∫ r, ind u v r * ind u' v' r ∂(volume.restrict (Set.Ico (0 : ℝ) T)) = ov u v u' v' := by
  unfold ov
  simp_rw [ind_mul]
  have hsub : Set.Ico (max (u : ℝ) u') (min (v : ℝ) v') ⊆ Set.Ico 0 T := fun r hr =>
    ⟨le_trans (le_trans (NNReal.coe_nonneg u) (le_max_left _ _)) hr.1,
      lt_of_lt_of_le hr.2 (le_trans (min_le_left _ _) (by exact_mod_cast hvT))⟩
  rw [integral_indicator_const (1 : ℝ) measurableSet_Ico, measureReal_restrict_apply measurableSet_Ico,
    Set.inter_eq_left.2 hsub, Real.volume_real_Ico, smul_eq_mul, mul_one]

/-- Elementary adapted processes `Y 1_[u,v)` on `[0,T]`. -/
structure Elem (m : ℝ≥0 → MeasurableSpace Ω) (T : ℝ≥0) where
  u : ℝ≥0
  v : ℝ≥0
  huv : u ≤ v
  hvT : v ≤ T
  Y : Ω → ℝ
  hY : Measurable[m u] Y
  C : ℝ
  hC : ∀ ω, |Y ω| ≤ C

/-- The time-space function of an elementary process. -/
noncomputable def efun {T : ℝ≥0} (i : Elem m T) (z : ℝ × Ω) : ℝ := ind i.u i.v z.1 * i.Y z.2

/-- The elementary stochastic integral. -/
noncomputable def ifun {T : ℝ≥0} (W : ℝ≥0 → Ω → ℝ) (i : Elem m T) (ω : Ω) : ℝ :=
  i.Y ω * (W i.v ω - W i.u ω)

lemma memLp_efun (hle : ∀ t, m t ≤ mΩ) {T : ℝ≥0} (i : Elem m T) :
    MemLp (efun i) 2 (μT P T) := by
  have hm : Measurable (efun i) :=
    ((ind_meas i.u i.v).comp measurable_fst).mul ((i.hY.mono (hle i.u) le_rfl).comp measurable_snd)
  refine MemLp.of_bound hm.aestronglyMeasurable i.C (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, efun, abs_mul]
  calc |ind i.u i.v z.1| * |i.Y z.2| ≤ 1 * |i.Y z.2| :=
        mul_le_mul_of_nonneg_right (ind_abs_le _ _ _) (abs_nonneg _)
    _ ≤ i.C := by rw [one_mul]; exact i.hC z.2

lemma memLp_ifun (hW : IncrHyp m W P) {T : ℝ≥0} (i : Elem m T) : MemLp (ifun W i) 2 P := by
  refine ((hW.mem2 i.u i.v).const_mul i.C).of_le
    ((i.hY.mono (hW.le i.u) le_rfl).aestronglyMeasurable.mul (hW.mem2 i.u i.v).aestronglyMeasurable)
    (Eventually.of_forall fun ω => ?_)
  simp only [ifun, Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right ((i.hC ω).trans (le_abs_self _)) (abs_nonneg _)

noncomputable def eE (hle : ∀ t, m t ≤ mΩ) (T : ℝ≥0) (i : Elem m T) : Lp ℝ 2 (μT P T) :=
  (memLp_efun (P := P) hle i).toLp _

noncomputable def eI (hW : IncrHyp m W P) (T : ℝ≥0) (i : Elem m T) : Lp ℝ 2 P :=
  (memLp_ifun hW i).toLp _

lemma inner_eE (hle : ∀ t, m t ≤ mΩ) {T : ℝ≥0} (i j : Elem m T) :
    ⟪eE (P := P) hle T i, eE hle T j⟫_ℝ = ov i.u i.v j.u j.v * ∫ ω, i.Y ω * j.Y ω ∂P := by
  unfold eE
  rw [L2.inner_def]
  have h1 := (memLp_efun (P := P) hle i).coeFn_toLp
  have h2 := (memLp_efun (P := P) hle j).coeFn_toLp
  have hc : ∫ z, ⟪((memLp_efun (P := P) hle i).toLp _ : ℝ × Ω → ℝ) z,
      ((memLp_efun (P := P) hle j).toLp _ : ℝ × Ω → ℝ) z⟫_ℝ ∂(μT P T) =
      ∫ z, (ind i.u i.v z.1 * ind j.u j.v z.1) * (i.Y z.2 * j.Y z.2) ∂(μT P T) := by
    refine integral_congr_ae ?_
    filter_upwards [h1, h2] with z hz1 hz2
    rw [hz1, hz2, RCLike.inner_apply', conj_trivial, efun, efun]
    ring
  rw [hc, μT, integral_prod_mul (fun r => ind i.u i.v r * ind j.u j.v r)
    (fun ω => i.Y ω * j.Y ω), int_time T i.hvT]

lemma inner_eI (hW : IncrHyp m W P) {T : ℝ≥0} (i j : Elem m T) :
    ⟪eI hW T i, eI hW T j⟫_ℝ = ov i.u i.v j.u j.v * ∫ ω, i.Y ω * j.Y ω ∂P := by
  unfold eI
  rw [L2.inner_def]
  have h1 := (memLp_ifun hW i).coeFn_toLp
  have h2 := (memLp_ifun hW j).coeFn_toLp
  have hc : ∫ ω, ⟪((memLp_ifun hW i).toLp _ : Ω → ℝ) ω, ((memLp_ifun hW j).toLp _ : Ω → ℝ) ω⟫_ℝ ∂P =
      ∫ ω, (i.Y ω * (W i.v ω - W i.u ω)) * (j.Y ω * (W j.v ω - W j.u ω)) ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [h1, h2] with z hz1 hz2
    rw [hz1, hz2, RCLike.inner_apply', conj_trivial, ifun, ifun]
  rw [hc, cov hW i.huv j.huv i.hY j.hY i.hC j.hC, mul_comm]

noncomputable def eL (hle : ∀ t, m t ≤ mΩ) (T : ℝ≥0) :
    (Elem m T →₀ ℝ) →ₗ[ℝ] Lp ℝ 2 (μT P T) :=
  Finsupp.linearCombination ℝ (eE hle T)

noncomputable def TL (hW : IncrHyp m W P) (T : ℝ≥0) : (Elem m T →₀ ℝ) →ₗ[ℝ] Lp ℝ 2 P :=
  Finsupp.linearCombination ℝ (eI hW T)

lemma inner_TL (hW : IncrHyp m W P) (T : ℝ≥0) (s t : Elem m T →₀ ℝ) :
    ⟪TL hW T s, TL hW T t⟫_ℝ = ⟪eL (P := P) hW.le T s, eL hW.le T t⟫_ℝ := by
  induction s using Finsupp.induction_linear with
  | zero => simp
  | add s1 s2 h1 h2 => simp only [map_add, inner_add_left, h1, h2]
  | single i a =>
    induction t using Finsupp.induction_linear with
    | zero => simp
    | add t1 t2 h1 h2 => simp only [map_add, inner_add_right, h1, h2]
    | single j b =>
      simp only [TL, eL, Finsupp.linearCombination_single, real_inner_smul_left,
        real_inner_smul_right, inner_eI, inner_eE]

lemma norm_TL (hW : IncrHyp m W P) (T : ℝ≥0) (s : Elem m T →₀ ℝ) :
    ‖TL hW T s‖ = ‖eL (P := P) hW.le T s‖ := by
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner, inner_TL]



end StochCalcO3

/-! O3M (8c066573 relay 17, O3 model instantiation): `B` and `B~` satisfy `StochCalcO3.IncrHyp` w.r.t. `M.F`,
so every `f ∈ L²(P)` has representing integrands `a, b ∈ L²(dt|[0,T) ⊗ P)` (in the closure of adapted simple processes):
`E[f Y (B_v - B_u)] = ∫∫ a 1_[u,v) Y` and `E[f Y (B~_v - B~_u)] = ∫∫ b 1_[u,v) Y`.
Append after probe/8c066573_S1RA.lean + RieszIso.lean body + O3gen_tail.lean (no import lines). -/

namespace StochCalcO3M

open HedgePSNV StochCalcBr StochCalcO3 StochCalcD3 StochCalcR1M StochCalcTiltM StochCalcSteinM
  StochCalcGauss StochCalcP6S

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]





end StochCalcO3M

/-! O4gen (8c066573 relay 17, O4 generic part; append after O3gen_tail.lean, Mathlib only).
If elementary combinations `s n` have time-space classes `eL (s n) → ψ` in `L²(μT)` and elementary integrals
`TL (s n) → J` in measure, then `J` has an `L²` version `K` with `‖K‖ = ‖ψ‖` (isometry) and `⟪f, K⟫ = ⟪a, ψ⟫`
for the representing integrand `a` of `f` (O3).  Plus pointwise formulas `coe_TL` / `coe_eL` for combinations. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}



lemma coe_TL (hW : IncrHyp m W P) (T : ℝ≥0) (s : Elem m T →₀ ℝ) :
    (TL hW T s : Ω → ℝ) =ᵐ[P] fun ω => s.sum (fun i c => c * ifun W i ω) := by
  induction s using Finsupp.induction_linear with
  | zero =>
    filter_upwards [Lp.coeFn_zero (E := ℝ) (p := 2) (μ := P)] with ω h
    rw [map_zero, h]
    simp
  | add s1 s2 h1 h2 =>
    rw [map_add]
    filter_upwards [Lp.coeFn_add (TL hW T s1) (TL hW T s2), h1, h2] with ω h h1 h2
    rw [h, Pi.add_apply, h1, h2,
      Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
  | single i c =>
    simp only [TL, Finsupp.linearCombination_single, Finsupp.sum_single_index, zero_mul]
    filter_upwards [Lp.coeFn_smul c (eI hW T i), (memLp_ifun hW i).coeFn_toLp] with ω h h'
    rw [h, Pi.smul_apply, eI, h', smul_eq_mul]

lemma coe_eL (hle : ∀ t, m t ≤ mΩ) (T : ℝ≥0) (s : Elem m T →₀ ℝ) :
    (eL (P := P) hle T s : ℝ × Ω → ℝ) =ᵐ[μT P T] fun z => s.sum (fun i c => c * efun i z) := by
  induction s using Finsupp.induction_linear with
  | zero =>
    filter_upwards [Lp.coeFn_zero (E := ℝ) (p := 2) (μ := μT P T)] with z h
    rw [map_zero, h]
    simp
  | add s1 s2 h1 h2 =>
    rw [map_add]
    filter_upwards [Lp.coeFn_add (eL (P := P) hle T s1) (eL hle T s2), h1, h2] with z h h1 h2
    rw [h, Pi.add_apply, h1, h2,
      Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
  | single i c =>
    simp only [eL, Finsupp.linearCombination_single, Finsupp.sum_single_index, zero_mul]
    filter_upwards [Lp.coeFn_smul c (eE (P := P) hle T i),
      (memLp_efun (P := P) hle i).coeFn_toLp] with z h h'
    rw [h, Pi.smul_apply, eE, h', smul_eq_mul]

end StochCalcO3

/-! O4step (8c066573 relay 18, O4 generic step-approximation part).  Append after O4gen_tail.lean.
Needs `Definitions.Def_EthierKurtz_itoStepValue`, `Definitions.Def_EthierKurtz_itoStepSum` and
`Solutions.Sol_pv_1558a108` (ItoLib) imported.
`O4fun`: function form of O4gen.  `O4step`: given EK approximants `a0` of a BOUNDED jointly measurable
integrand `H` (integrated squared error → 0 in probability, step sums → `J` in probability) and the ItoLib
"zero lemma" for step sums, the approximants clamped at the bound of `H` are elementary combinations whose
time-space classes converge to `H` in `L²(μT)` and whose integrals still converge to `J`; hence
`∫ f J dP = ∫ a H dμT` for the representing integrand `a` of `f` (O3). -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology EthierKurtz ItoLib
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}



/-! Clamping and step values. -/








/-! The clamped approximants as elementary combinations. -/











end StochCalcO3

/-! O4 model (8c066573 relay 18; append after O4step_tail.lean in the model dev file).
The doubly stopped simple strategy `θ = Y 1{s∧τ ≤ u < s'∧τ}`, `τ = hitR X R ∧ hitR σ R'`, is admissible
(`dblSimple_mem_AX`) and its Itô integrand `θ X σ` is bounded by `C R R'`, so `O4step` gives
`E[f · Y (J_{s'∧τ} - J_{s∧τ})] = ∫ a θ X σ dμT` for the representing integrand `a` of `f` (O3, dB part). -/

namespace StochCalcO4M

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1b StochCalcO3 StochCalcO3M StochCalcS1R StochCalcHit
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]











end StochCalcO4M
/-! O5 drift identity (8c066573 relay 19; append after O4M_tail.lean in the model dev file).
Triple stop `τ = hitR X R ∧ hitR σ R' ∧ hitR μ R''` bounds both integrands `θ X σ` and `θ X μ`.
KEY (relay 19): no conditional expectation `f_u` is needed for the drift: Fubini alone gives
`E[f ∫_0^T θ X μ du] = ∫ (θ X μ)(u,ω) f(ω) dμT`.  With O4 and `f ⊥ χ_T`:
`O5_gain : ∫ a θ X σ dμT + ∫ θ X μ f dμT = 0` for every triple-stopped simple strategy. -/

namespace StochCalcO5

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1b StochCalcO3 StochCalcO3M StochCalcS1R StochCalcHit StochCalcO4M
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]










end StochCalcO5
/-! O6a (8c066573 relay 19): Pred-membership of bounded step-approximable integrands.
Append after O56_tail.lean.  `pred_approx` = the L²(μT) half of O4step (no stochastic integral):
any bounded jointly measurable `H` whose dyadic step approximants `a0` (adapted, NOT necessarily
bounded) have integrated squared error → 0 in probability is an `L²(μT)` limit of elementary
combinations; `pred_mem` states it as membership of the class of `H` in the closure of `range eL`. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology EthierKurtz ItoLib
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω}



end StochCalcO3

/-! O6b (8c066573 relay 20): left-point sampling.  Append after O6a_tail.lean.
`pred_left`: a bounded, jointly measurable, adapted process that is left-continuous in time at
a.e. `u ∈ (0,T]` (for every `ω`) has its class in the closure of `range eL` (dyadic left-point
approximants `a0 n k = H (k T / 2^n)`, dominated convergence, a.e. ⇒ in measure). -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology EthierKurtz ItoLib
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω}




end StochCalcO3

/-! O6c (8c066573 relay 20): generic Hilbert pieces of O6.  Append after O6b_tail.lean.
`O6_core`: an `L²(μT)` function in the closure of `range eL` orthogonal to every elementary
`efun` vanishes a.e.;  `perp_all`: orthogonality to elementaries with `v < T` suffices;
`proj_fun`: predictable projection `c` of any `F ∈ L²(μT)` (`∫ c ψ = ∫ F ψ` for predictable `ψ`);
`pred_mul`: predictable × bounded adapted a.e.-left-continuous is predictable. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology EthierKurtz ItoLib
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω}








lemma ae_fst_Ico (T : ℝ≥0) : ∀ᵐ z ∂(μT P T), z.1 ∈ Set.Ico (0 : ℝ) T :=
  Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ico)




/-- The predictable subspace of `L²(μT)`. -/
noncomputable def Pred (hle : ∀ t, m t ≤ mΩ) (T : ℝ≥0) : Submodule ℝ (Lp ℝ 2 (μT P T)) :=
  (LinearMap.range (eL (P := P) hle T)).topologicalClosure

lemma mem_Pred_iff (hle : ∀ t, m t ≤ mΩ) (T : ℝ≥0) (x : Lp ℝ 2 (μT P T)) :
    x ∈ Pred (P := P) hle T ↔ x ∈ closure (Set.range (eL (P := P) hle T)) := by
  rw [Pred, ← SetLike.mem_coe, Submodule.topologicalClosure_coe, LinearMap.coe_range]




end StochCalcO3

/-! O6M (8c066573 relay 20): model instance of O6.  Append after O6c_tail.lean in the model dev
file (O6a.lean + O6b_tail + O6c_tail).  With `a' = proj a`, `c = proj (f ∘ snd)` (predictable
projections), every triple stop `τ_N` gives `w_N = a' (Xσ 1[·<τ_N]) + c (Xμ 1[·<τ_N]) ⊥ elementaries`
(O5_gain + proj_fun) and `w_N` predictable (pred_mul), so `w_N = 0` (O6_core); `τ_N = T`
eventually (continuous paths are bounded on `[0,T]`), hence `a' Xσ + c Xμ = 0` μT-a.e. -/

namespace StochCalcO6M

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1b StochCalcO3 StochCalcO3M StochCalcS1R StochCalcHit StochCalcO4M
open StochCalcO5
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]










end StochCalcO6M



/-! O7.1 [U1] energy uniqueness, bounded-coefficient core.  Restriction `resF s` of elementary
combinations to `[0,s)`, its orthogonality to `m s`, and the restricted-norm bound
`‖E[θ | m s]‖ ≤ ‖a 1_{[0,s)}‖` for a stochastic integral `θ` with integrand `a`. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}

/-- Restriction of an elementary process to `[0,s)`. -/
noncomputable def resI {T : ℝ≥0} (s : ℝ≥0) (i : Elem m T) : Elem m T where
  u := i.u
  v := max i.u (min i.v s)
  huv := le_max_left _ _
  hvT := max_le (i.huv.trans i.hvT) ((min_le_left _ _).trans i.hvT)
  Y := i.Y
  hY := i.hY
  C := i.C
  hC := i.hC

lemma ind_resI {T : ℝ≥0} (s : ℝ≥0) (i : Elem m T) (r : ℝ) :
    ind (resI s i).u (resI s i).v r = ind i.u i.v r * ind 0 s r := by
  have hu : (0 : ℝ) ≤ i.u := i.u.2
  simp only [resI, ind, Set.indicator_apply, Set.mem_Ico, NNReal.coe_max, NNReal.coe_min,
    NNReal.coe_zero, lt_max_iff, lt_min_iff]
  by_cases h1 : (i.u : ℝ) ≤ r
  · have h1' : ¬ r < (i.u : ℝ) := not_lt.2 h1
    have h0 : (0 : ℝ) ≤ r := hu.trans h1
    by_cases h2 : r < (i.v : ℝ)
    · by_cases h3 : r < (s : ℝ)
      · simp [h1, h1', h2, h3, h0]
      · simp [h1, h1', h2, h3]
    · simp [h1, h1', h2]
  · simp [h1]

lemma efun_resI {T : ℝ≥0} (s : ℝ≥0) (i : Elem m T) (z : ℝ × Ω) :
    efun (resI s i) z = efun i z * ind 0 s z.1 := by
  simp only [efun, ind_resI]
  show ind i.u i.v z.1 * ind 0 s z.1 * i.Y z.2 = _
  ring

/-- Restriction of a combination. -/
noncomputable def resF {T : ℝ≥0} (s : ℝ≥0) (x : Elem m T →₀ ℝ) : Elem m T →₀ ℝ :=
  Finsupp.mapDomain (resI s) x

lemma comb_resF {T : ℝ≥0} (s : ℝ≥0) (x : Elem m T →₀ ℝ) (z : ℝ × Ω) :
    (resF s x).sum (fun i c => c * efun i z) = x.sum (fun i c => c * efun i z) * ind 0 s z.1 := by
  unfold resF
  rw [Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
  simp only [efun_resI, Finsupp.sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma int_ifun_res (hW : IncrHyp m W P) {T : ℝ≥0} (s : ℝ≥0) (i : Elem m T) {g : Ω → ℝ}
    (hg : Measurable[m s] g) :
    ∫ ω, g ω * (ifun W i ω - ifun W (resI s i) ω) ∂P = 0 := by
  by_cases hvs : i.v ≤ s
  · have hv : (resI s i).v = i.v := by
      show max i.u (min i.v s) = i.v
      rw [min_eq_left hvs, max_eq_right i.huv]
    have h0 : ∀ ω, g ω * (ifun W i ω - ifun W (resI s i) ω) = 0 := by
      intro ω
      simp only [ifun, hv]
      show g ω * (i.Y ω * (W i.v ω - W i.u ω) - i.Y ω * (W i.v ω - W i.u ω)) = 0
      ring
    simp_rw [h0, integral_zero]
  · push Not at hvs
    have hv : (resI s i).v = max i.u s := by
      show max i.u (min i.v s) = max i.u s
      rw [min_eq_right hvs.le]
    have key : ∀ ω, g ω * (ifun W i ω - ifun W (resI s i) ω) =
        (g ω * i.Y ω) * (W i.v ω - W (max i.u s) ω) := by
      intro ω
      simp only [ifun, hv]
      show g ω * (i.Y ω * (W i.v ω - W i.u ω) - i.Y ω * (W (max i.u s) ω - W i.u ω)) = _
      ring
    simp_rw [key]
    refine int_mul_dW hW (max_le i.huv hvs.le) ?_
    exact (hg.mono (hW.mono (le_max_right _ _)) le_rfl).mul
      (i.hY.mono (hW.mono (le_max_left _ _)) le_rfl)

lemma int_TL_res (hW : IncrHyp m W P) (T : ℝ≥0) (s : ℝ≥0) (x : Elem m T →₀ ℝ) {g : Ω → ℝ}
    (hg : Measurable[m s] g) (hg2 : MemLp g 2 P) :
    ∫ ω, g ω * (TL hW T x ω - TL hW T (resF s x) ω) ∂P = 0 := by
  have e : (fun ω => g ω * (TL hW T x ω - TL hW T (resF s x) ω)) =ᵐ[P]
      fun ω => ∑ i ∈ x.support, x i * (g ω * (ifun W i ω - ifun W (resI s i) ω)) := by
    filter_upwards [coe_TL hW T x, coe_TL hW T (resF s x)] with ω h1 h2
    rw [h1, h2]
    unfold resF
    rw [Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
    simp only [Finsupp.sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [integral_congr_ae e, integral_finsetSum]
  · refine Finset.sum_eq_zero fun i _ => ?_
    rw [integral_const_mul, int_ifun_res hW s i hg, mul_zero]
  · intro i _
    refine Integrable.const_mul ?_ _
    exact hg2.integrable_mul ((memLp_ifun hW i).sub (memLp_ifun hW (resI s i)))

/-- The restricted integrand `a 1_{[0,s)}` as an `L²` element. -/
lemma memLp_res {T : ℝ≥0} {a : ℝ × Ω → ℝ} (ha : MemLp a 2 (μT P T)) (s : ℝ≥0) :
    MemLp (fun z => a z * ind 0 s z.1) 2 (μT P T) := by
  refine ha.of_le (ha.aestronglyMeasurable.mul
    ((ind_meas 0 s).comp measurable_fst).aestronglyMeasurable) (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (ind_abs_le _ _ _)

lemma norm_res_sub_le (hle : ∀ t, m t ≤ mΩ) {T : ℝ≥0} (a : Lp ℝ 2 (μT P T)) (s : ℝ≥0)
    (x : Elem m T →₀ ℝ) :
    ‖eL (P := P) hle T (resF s x) - (memLp_res (Lp.memLp a) s).toLp _‖ ≤
      ‖eL (P := P) hle T x - a‖ := by
  refine Lp.norm_le_norm_of_ae_le ?_
  filter_upwards [Lp.coeFn_sub (eL (P := P) hle T (resF s x)) ((memLp_res (Lp.memLp a) s).toLp _),
    Lp.coeFn_sub (eL (P := P) hle T x) a, coe_eL (P := P) hle T (resF s x), coe_eL (P := P) hle T x,
    (memLp_res (Lp.memLp a) s).coeFn_toLp] with z h1 h2 h3 h4 h5
  rw [h1, h2, Pi.sub_apply, Pi.sub_apply, h3, h4, h5, comb_resF, ← sub_mul, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (ind_abs_le _ _ _)

/-- If `TL x_n → θ` and `a ∈ Pred` represents `θ`, then `eL x_n → a`. -/
theorem eL_tendsto (hW : IncrHyp m W P) (T : ℝ≥0) {θ : Lp ℝ 2 P} {a : Lp ℝ 2 (μT P T)}
    (ha : ∀ x, ⟪θ, TL hW T x⟫_ℝ = ⟪a, eL (P := P) hW.le T x⟫_ℝ)
    (haP : a ∈ closure (Set.range (eL (P := P) hW.le T)))
    {x : ℕ → (Elem m T →₀ ℝ)} (hx : Tendsto (fun n => TL hW T (x n)) atTop (𝓝 θ)) :
    Tendsto (fun n => eL (P := P) hW.le T (x n)) atTop (𝓝 a) := by
  have hc : CauchySeq fun n => eL (P := P) hW.le T (x n) := by
    have hcu : CauchySeq fun n => TL hW T (x n) := hx.cauchySeq
    rw [Metric.cauchySeq_iff] at hcu ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hcu ε hε
    refine ⟨N, fun i hi j hj => ?_⟩
    rw [dist_eq_norm, ← map_sub, ← norm_TL hW T, map_sub, ← dist_eq_norm]
    exact hN i hi j hj
  obtain ⟨ψ, hψ⟩ := cauchySeq_tendsto_of_complete hc
  have hψP : ψ ∈ closure (Set.range (eL (P := P) hW.le T)) :=
    mem_closure_of_tendsto hψ (Eventually.of_forall fun n => ⟨x n, rfl⟩)
  have horth : ∀ y, ⟪a - ψ, eL (P := P) hW.le T y⟫_ℝ = 0 := by
    intro y
    have h1 : Tendsto (fun n => ⟪TL hW T (x n), TL hW T y⟫_ℝ) atTop (𝓝 ⟪θ, TL hW T y⟫_ℝ) :=
      hx.inner tendsto_const_nhds
    have h2 : Tendsto (fun n => ⟪eL (P := P) hW.le T (x n), eL (P := P) hW.le T y⟫_ℝ) atTop
        (𝓝 ⟪ψ, eL (P := P) hW.le T y⟫_ℝ) := hψ.inner tendsto_const_nhds
    simp only [inner_TL] at h1
    rw [inner_sub_left, ← ha y, tendsto_nhds_unique h1 h2, sub_self]
  have hcl : closure (Set.range (eL (P := P) hW.le T)) ⊆ {w | ⟪a - ψ, w⟫_ℝ = 0} :=
    closure_minimal (by rintro _ ⟨y, rfl⟩; exact horth y)
      (isClosed_eq (continuous_const.inner continuous_id) continuous_const)
  have hmem : a - ψ ∈ closure (Set.range (eL (P := P) hW.le T)) := by
    have := (Pred (P := P) hW.le T).sub_mem ((mem_Pred_iff hW.le T a).2 haP)
      ((mem_Pred_iff hW.le T ψ).2 hψP)
    exact (mem_Pred_iff hW.le T _).1 this
  have h0 : a - ψ = 0 := inner_self_eq_zero.1 (hcl hmem)
  rw [sub_eq_zero.1 h0]
  exact hψ

end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}

omit [IsProbabilityMeasure P] in
lemma sq_norm_toLp {μ : Measure (ℝ × Ω)} {F : ℝ × Ω → ℝ} (hF : MemLp F 2 μ) :
    ‖hF.toLp F‖ ^ 2 = ∫ z, F z ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hF.coeFn_toLp] with z h
  rw [h, RCLike.inner_apply', conj_trivial, sq]


/-- **S1**: pairing of `θ = I(a)` with an `m s`-measurable `g` sees only `a 1_{[0,s)}`. -/
theorem S1 (hW : IncrHyp m W P) (T : ℝ≥0) {θ : Lp ℝ 2 P}
    (hθ : θ ∈ closure (Set.range (TL hW T)))
    {a : Lp ℝ 2 (μT P T)} (ha : ∀ x, ⟪θ, TL hW T x⟫_ℝ = ⟪a, eL (P := P) hW.le T x⟫_ℝ)
    (haP : a ∈ closure (Set.range (eL (P := P) hW.le T))) (s : ℝ≥0)
    {g : Ω → ℝ} (hg : Measurable[m s] g) (hg2 : MemLp g 2 P) :
    ⟪θ, hg2.toLp g⟫_ℝ ≤ ‖(memLp_res (Lp.memLp a) s).toLp _‖ * ‖hg2.toLp g‖ := by
  obtain ⟨xs, hxr, hx⟩ := mem_closure_iff_seq_limit.1 hθ
  choose y hy using hxr
  have hx' : Tendsto (fun n => TL hW T (y n)) atTop (𝓝 θ) := by
    simp_rw [hy]; exact hx
  have hEa := eL_tendsto hW T ha haP hx'
  have hres : Tendsto (fun n => eL (P := P) hW.le T (resF s (y n))) atTop
      (𝓝 ((memLp_res (Lp.memLp a) s).toLp _)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => norm_res_sub_le hW.le a s (y n)) ?_
    exact tendsto_iff_norm_sub_tendsto_zero.1 hEa
  have heq : ∀ n, ⟪TL hW T (y n), hg2.toLp g⟫_ℝ = ⟪TL hW T (resF s (y n)), hg2.toLp g⟫_ℝ := by
    intro n
    have h0 : ⟪TL hW T (y n) - TL hW T (resF s (y n)), hg2.toLp g⟫_ℝ = 0 := by
      rw [L2.inner_def]
      refine (integral_congr_ae ?_).trans (int_TL_res hW T s (y n) hg hg2)
      filter_upwards [Lp.coeFn_sub (TL hW T (y n)) (TL hW T (resF s (y n))), hg2.coeFn_toLp]
        with ω h1 h2
      rw [h1, h2, Pi.sub_apply, RCLike.inner_apply', conj_trivial, mul_comm]
    rw [inner_sub_left, sub_eq_zero] at h0
    exact h0
  have hlim1 : Tendsto (fun n => ⟪TL hW T (resF s (y n)), hg2.toLp g⟫_ℝ) atTop
      (𝓝 ⟪θ, hg2.toLp g⟫_ℝ) := by
    simp_rw [← heq]; exact hx'.inner tendsto_const_nhds
  have hlim2 : Tendsto (fun n => ‖eL (P := P) hW.le T (resF s (y n))‖ * ‖hg2.toLp g‖) atTop
      (𝓝 (‖(memLp_res (Lp.memLp a) s).toLp _‖ * ‖hg2.toLp g‖)) :=
    hres.norm.mul_const _
  refine le_of_tendsto_of_tendsto' hlim1 hlim2 fun n => ?_
  rw [← norm_TL hW T]
  exact real_inner_le_norm _ _


end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}











end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}



end StochCalcO3

/-! O7.1 localization, part L0.  `Rep θ b` : `θ` is the stochastic integral of the predictable
integrand `b` (isometric extension of `TL`).  Basic calculus of `Rep` (distance identity, limits,
existence, uniqueness, orthogonality to `L²(m s)` when `b` vanishes before `s`) and the locality
lemma `L0`: for `A ∈ m t` and `b` vanishing before `t`, `Rep θ b → Rep (1_A θ) (1_A b)`. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}

/-- `θ` is the stochastic integral of the predictable integrand `b`. -/
def Rep (hW : IncrHyp m W P) (T : ℝ≥0) (θ : Lp ℝ 2 P) (b : Lp ℝ 2 (μT P T)) : Prop :=
  θ ∈ closure (Set.range (TL hW T)) ∧ b ∈ closure (Set.range (eL (P := P) hW.le T)) ∧
    ∀ x, ⟪θ, TL hW T x⟫_ℝ = ⟪b, eL (P := P) hW.le T x⟫_ℝ

lemma rep_dist (hW : IncrHyp m W P) (T : ℝ≥0) {θ : Lp ℝ 2 P} {b : Lp ℝ 2 (μT P T)}
    (h : Rep hW T θ b) (x : Elem m T →₀ ℝ) :
    ‖TL hW T x - θ‖ = ‖eL (P := P) hW.le T x - b‖ := by
  obtain ⟨hθ, hb, hi⟩ := h
  obtain ⟨xs, hxr, hx⟩ := mem_closure_iff_seq_limit.1 hθ
  choose y hy using hxr
  have hx' : Tendsto (fun n => TL hW T (y n)) atTop (𝓝 θ) := by simp_rw [hy]; exact hx
  have hE := eL_tendsto hW T hi hb hx'
  have h1 : Tendsto (fun n => ‖TL hW T x - TL hW T (y n)‖) atTop (𝓝 ‖TL hW T x - θ‖) :=
    (tendsto_const_nhds.sub hx').norm
  have h2 : Tendsto (fun n => ‖eL (P := P) hW.le T x - eL (P := P) hW.le T (y n)‖) atTop
      (𝓝 ‖eL (P := P) hW.le T x - b‖) := (tendsto_const_nhds.sub hE).norm
  have he : ∀ n, ‖TL hW T x - TL hW T (y n)‖ =
      ‖eL (P := P) hW.le T x - eL (P := P) hW.le T (y n)‖ := by
    intro n; rw [← map_sub, ← map_sub, norm_TL]
  simp_rw [he] at h1
  exact tendsto_nhds_unique h1 h2
























end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}

/-! L1: grid stopping times.  For `τ` with finitely many values `t ∈ S` (`{τ = t} ∈ m t`) and
`δ = I(1_{τ ≤ r} a)`, `δ ⊥ ξ 1_{u < τ}` for bounded `m u`-measurable `ξ`. -/












end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}

/-! L2: general stopping times `τ ≤ T`, by the dyadic ceilings `gc T n τ ↓ τ`. -/


















end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}






end StochCalcO3

/-! (B1) cutting a predictable integrand at a stopping time keeps it predictable. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}





end StochCalcO3
-- O7B2 tail (8c066573 relay 24): append after probe/8c066573_B.lean (= L0.lean + O7B_tail).

/-! (B2) the cut-off integral `δ = I(1_{τ ≤ r} a)` is orthogonal to `1_{r<τ} ψ`, and
(B3) the projections of `θ` and of `θ - δ` agree before `τ`. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}






end StochCalcO3

/-! O7.1 (U1, general): energy uniqueness for `a = -η c` with `η` continuous adapted. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}



end StochCalcO3

/-! O7.2 (8c066573 relay 25): K-projection.  Two filtrations `mK ≤ mF` for which the same process
`W` satisfies `IncrHyp`, plus the conditional-independence hypothesis
`H1 : E[Y | mK T] = E[Y | mK u]` for bounded `mF u`-measurable `Y` (`u ≤ T`).  If `θ = I_F(a)`
then `φ = E[θ | mK T]` is a K-stochastic integral `I_K(b)`, where `b` is the orthogonal projection
of `a` onto the K-predictable subspace: `⟪b, ψ⟫ = ⟪a, ψ⟫` for every K-predictable `ψ`. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {W : ℝ≥0 → Ω → ℝ}












end StochCalcO3

/-! O7.4a (8c066573 relay 25): identification of an integrand from localized weak pairings.
If `b, c'` are predictable and `⟪b, 1_{r<τ_R} e⟫ = -⟪c', η 1_{r<τ_R} e⟫` for every elementary `e`
and every hitting level `R ∈ ℕ` of the continuous adapted `η`, then `b = -η c'` a.e.  (This turns the
K-projection `Kproj` of `a = -η c` into the hypothesis `hac` of `U1` without assuming `η` bounded.) -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω}






end StochCalcO3

/-! O7.4b (8c066573 relay 25): `Kshift`.  If `θ = I_F(a)` with `a = -η c`, `c` the F-projection of
`θ`, and `η` continuous and K-adapted, then `φ = E[θ | mK T]` satisfies `φ = I_K(b)` with
`b = -η c_φ`, `c_φ` the K-projection of `φ` (the hypothesis shape of `U1` in the filtration K). -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {W : ℝ≥0 → Ω → ℝ}




end StochCalcO3

/-! O7.4c (8c066573 relay 25): `U1_diff` -- two integrals `θ₁ = I(-η c₁)`, `θ₂ = I(-η c₂)` (each `cᵢ`
the predictable projection of `θᵢ`, integrands vanishing before `v`) coincide.  O7.4 applies it in
the filtration K to `θ₁ = E[f | K_T] - f_t` (from `Kshift`) and `θ₂ = f_t (Z_T / Z_t - 1)` (from O7.3). -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}


end StochCalcO3

/-! O7.3 generic part (Z1): `Rep` is closed under `L²` limits of integrands (`rep_of_tendsto`),
and the truncation limit `rep_trunc`: integrands `1_{S n} f` (`S n` increasing, covering a.e.)
with `Rep θ_n (1_{S n} f)` and `‖θ_n‖ ≤ C` force `f ∈ L²(μT)` and `Rep θ f` for the `L²`
limit `θ` of `θ_n`.  Used for `Z_T - 1 = I(-Z η)` from the stopped identities. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}




end StochCalcO3

/-! Z6 (8c066573 relay 27, O7.3): L² optional-sampling bound for a right-continuous martingale
closed by `Z T`: `‖Z_{τ∧T}‖₂ ≤ ‖Z_T‖₂` for every stopping time `τ`.  Finite-valued case by
conditional Jensen on `{σ = t} ∈ m t` (`eLpNorm_condExp_le_eLpNorm`), general case by the
dyadic ceilings `gc T n τ ↓ τ ∧ T` and Fatou. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω}









end StochCalcO3

/-! Z4 (8c066573 relay 27, O7.3): Rep form of an EK Ito integral of a bounded integrand
(copy of O4step's approximation argument ending in `rep_exists`/`rep_conv`). -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology EthierKurtz ItoLib
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}



end StochCalcO3

/-! Z4t (8c066573 relay 27, O7.3): transfer of `Rep` from a larger filtration `m'` (e.g. the completed
Brownian past) to a smaller one `m ≤ m'` (e.g. `M.F`) when every `m' t`-measurable variable has an
a.e.-equal `m t`-measurable version: the elementary integrals and time-space classes agree. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {W : ℝ≥0 → Ω → ℝ}




end StochCalcO3

/-! Z5 (8c066573 relay 28, O7.3): stopped identification.  If `Rep θ a` and `K t =ᵐ E[θ | m t]`
(t ≤ T) with right-continuous paths, then for a stopping time `τ ≤ T` the variable `K_τ` is the
integral of `1_{s<τ} a`.  Route: (rep_aesm) integrals of integrands vanishing after `s` are
`m s`-measurable; (rep_ce) `E[θ|m t]` integrates `1_{s<t} a`; (Z5fin) finite-valued `τ` via `L0`;
(Z5) grid `gc T n τ ↓ τ`, `L²` limit + a.e. subsequence + right-continuity. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}








end StochCalcO3

/-! Z4m-a (8c066573 relay 28, O7.3): completed-Brownian-past measurable variables have
`M.F t`-measurable a.e. versions (append after Br.lean; needs `import Solutions.Sol_pv_1558a108`
for `ItoLib.aeClosure` / `completedBrownianPast_const_le`). -/

namespace StochCalcZ4m

open MeasureTheory ProbabilityTheory Filter HedgePSNV EthierKurtz ItoLib StochCalcBr
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

section Gen
variable {Ω' : Type*}



end Gen






end StochCalcZ4m

/-! Z4m-b (8c066573 relay 29, O7.3): a bounded library Ito integral (filtration `cBP`, driver
`W · · 0`) of the HedgePSNV model is represented (`Rep`, filtration `M.F`, driver `M.B`) by its
integrand.  `M.F`-measurable a.e. versions of the library approximants (hmod_cBP), clamped to keep
the per-level bounds, then `StochCalcO3.O4rep`. Append after the combined dev base (O6M + generic
Z chain + O7Z4m_tail). -/

namespace StochCalcZ4mb

open MeasureTheory ProbabilityTheory Filter HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcO3 StochCalcO3M StochCalcZ4m
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]



end StochCalcZ4mb


/-! Z2 (8c066573 relay 29, O7.3): a continuous, `cBP`-adapted version `Ic` of the Ito integral of
`η' s = η (s ∧ T)`, glued from the continuous Ito integrals of the clamped integrands `clamp n η'`
(platform theorem 1c98c8e0, conjunct 3, as the hypothesis `ContHyp M`).  Gluing index: the least
`n` with `sup |η'| ≤ n` (whole horizon) for the paths, and the least `n` with `sup_{[0,t]} |η'| ≤ n`
for the `cBP t`-measurable version at time `t` (completeness of `cBP t`).  Append after
O7Z4mb_tail. -/

namespace StochCalcZ2

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

















end StochCalcZ2



/-! Z3 (8c066573 relay 29, O7.3): Ito formula for `Zc = exp(-Ic - ½∫η'²)`: for a continuous,
`cBP`-adapted Ito integral `Ic` of `η'` (Z2), `Zc t = 1 + K t` a.s. for each `t`, where `K` is the
Ito integral of `-Zc η'` (ItoLib `ito_formula` with `e = 1`, `X = Ic + ½∫η'²`, `f x = exp(-x₀)`).
Append after O7Z2_tail. -/

namespace StochCalcZ3

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW StochCalcZ2
open scoped NNReal ENNReal

section line
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]





end line

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]












end StochCalcZ3

/-! Z7a (8c066573 relay 30, O7.3): horizon change for `Rep` (an integrand on `[0,t)` represents
the same variable at any later horizon `T`), hence the conditional expectation of a represented
variable at time `t` is represented at horizon `t`; model corollary `Jmart`: a bounded library Ito
integral is an `M.F`-martingale.  Append after O7Z3_tail. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}













end StochCalcO3

namespace StochCalcZ7a

open MeasureTheory ProbabilityTheory Filter HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcO3 StochCalcO3M StochCalcZ4m StochCalcZ4mb
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]


end StochCalcZ7a

/-! Z7b/Z7c (8c066573 relay 30, O7.3): `Zc` is continuous, `M.F`-adapted, a.e. equal to `M.Z`
on `[0,T]` and an `M.F`-martingale closed by `Zc T` (Assumption5); stopping at the hitting time
`τ R` of `|Zc η'| ≥ R`, the library Ito integral `J` of the clamped integrand `Hcl R` equals
`Zc - 1` at `τ R` (locality at dyadic `t < τ R` + path continuity).  Append after O7Z7a_tail. -/

namespace StochCalcZ7b

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW StochCalcZ2 StochCalcZ3 StochCalcZ4m StochCalcHit
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]






variable {Ic : ℝ≥0 → Ω → ℝ}
















end StochCalcZ7b

/-! Z7d (8c066573 relay 30, O7.3 assembly): `Zc T - 1` is represented (`Rep`, filtration `M.F`,
driver `M.B`) by the integrand `-Zc η'` on `[0,T)`, which is in `L²(dt × dP)`.  Per level `n`:
ContHyp integral `J n` of `Hcl n`, Z4m representative, Jmart (Z5's martingale hypothesis), Z5 at
`tau n`, locality `loc`, Z6 bound; then rep_trunc over `S n = {s < tau n}` and the a.e. limit
(`tau n = T` eventually).  Append after O7Z7b_tail. -/

namespace StochCalcZ7d

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW StochCalcZ2 StochCalcZ3 StochCalcZ4m StochCalcZ4mb StochCalcHit
open StochCalcO3 StochCalcO3M StochCalcZ7a StochCalcZ7b
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]



end StochCalcZ7d


/-! O7ZM (8c066573 relay 31, O7.3 remainder): multiplication of a stochastic integral by a
bounded `m t`-measurable factor `ζ` (generalizes `L0`, where `ζ = 1_A`), and the tail
representation `θ - E[θ | m t] = I(a 1_[t,T))`.  Generic `StochCalcO3`; append after O7Z7d. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}












end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω}








end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}


end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]


end StochCalcO3

/-! O7ZK (8c066573 relay 32, O7.3 model instance in a sub-filtration `mK`): generic
`rep_restrict` (an `mF`-representation of an `mK T`-measurable `θ` by an `mK`-predictable integrand
is an `mK`-representation), `mart_restrict` (tower property), and the model instance `zK` of `ztail`
for `ZT = Zc (· ∧ T)` in any filtration `cBP ≤ mK ≤ M.F` with `IncrHyp mK M.B` and `H1`.
Generic `StochCalcO3` part + `StochCalcZK`; append after O7ZM_tail. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {W : ℝ≥0 → Ω → ℝ}




end StochCalcO3

namespace StochCalcZK

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW StochCalcZ2 StochCalcZ3 StochCalcZ4m StochCalcZ4mb StochCalcHit
open StochCalcO3 StochCalcO3M StochCalcZ7a StochCalcZ7b StochCalcZ7d
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]




end StochCalcZK

/-! O7KF (8c066573 relay 32, model K + H1 for O7.4): the filtration
`Kf t s = F_s (s < t), F_t ⊔ G_s (s ≥ t)`, with `Kf ≤ F`, `IncrHyp (Kf t) M.B`, `Zc` and `η`
`Kf`-adapted on `[0,T]`, and the conditional-independence hypothesis `H1` of `Kproj`/`Kshift`.
Generic part: `ce_sup_indep` (`E[Y | A ⊔ D] = E[Y | A]` for `Y ∈ F' ⊇ A`, `F' ⊥ D`) and
`meas_of_ae_eq_nulls`.  Append after O7ZK_tail. -/

namespace StochCalcCE

open MeasureTheory ProbabilityTheory Filter

variable {Ω : Type*} {A F' D K : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]




end StochCalcCE

namespace StochCalcKF

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW StochCalcZ2 StochCalcZ3 StochCalcZ4m StochCalcZ4mb StochCalcHit
open StochCalcO3 StochCalcO3M StochCalcZ7a StochCalcZ7b StochCalcZ7d StochCalcCE StochCalcR1M
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

















end StochCalcKF

/-! O7Q1 (8c066573 relay 32, O7.4 generic core): if `θ = I_F(a)` with `a = -η c` (`c` the
F-projection of `θ`, `η` continuous `mK`-adapted) and `Θ = E[θ | mK T]` is orthogonal to `L∞(mK t)`,
then `Θ = 0`.  Kshift (Θ = I_K(-η cΘ)), perp_tail (cΘ = 0 before t), U1.  Append after O7KF_tail. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {W : ℝ≥0 → Ω → ℝ}


end StochCalcO3

/-! O7Q1M (8c066573 relay 33, O7.4 model): `E[θ | F_t ⊔ G_T] = E[θ|F_t] Z_T / Z_t` for `θ = I_F(-η c)`.
Generic: `int_mul_ce`, `proj_tailA` (F-projection of `1_A (θ - f_t)`).  Model: `Q1R` (fixed `R`), `Q1model`.
Append after O7Q1_tail. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]


variable {m : ℝ≥0 → MeasurableSpace Ω}


end StochCalcO3

namespace StochCalcQ1M

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW StochCalcZ2 StochCalcZ3 StochCalcZ4m StochCalcZ4mb StochCalcHit
open StochCalcO3 StochCalcO3M StochCalcZ7a StochCalcZ7b StochCalcZ7d StochCalcCE StochCalcR1M
open StochCalcZK StochCalcKF
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]



end StochCalcQ1M

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal Topology


set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace StochCalcHedge

open HedgePSNV







end StochCalcHedge

/-! S8 tail (8c066573 relay 1, 2026-11-06): `0 ≤ Z_t/Z^M_t ≤ 1` a.s. and the three elementary
conjuncts of theorem_1_ii (everything except the value formula (21)).
Appended after S8.lean (namespace StochCalcHedge provides I_zero_ae, Z_pos, Z_T_measurable,
ZM0_eq, one_lt_ZM0). -/

namespace StochCalcS8b

open HedgePSNV StochCalcHedge









end StochCalcS8b
/-! K2a (8c066573 relay 2, 2026-11-06): base change `P → P^M` for the `B~`-tilt machinery.
`dP^M/dP = Z_T` is `G_T`-measurable, so every independence `F_u ⊔ G_T ⊥ (B~ increments after u)`
and the Gaussian laws of the increments survive under `P^M`; the exponential `B~`-tilts of `P^M`
are in `M_X` once `X` is a `P^M`-martingale (no L² assumption on `X`).
Append after cc6d45ce_P4.lean + S8.lean + S8b_tail.lean (imports stripped). -/

namespace StochCalcK2

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt StochCalcTiltM
  StochCalcSteinM

section generic

variable {Ω : Type*}





end generic

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]




















end StochCalcK2
/-! K2b (8c066573 relay 2): orthogonality `E^M[Y ξ χ_T] = 0` and the Stein identity under `P^M`.
Append after K2a_tail.lean. -/

namespace StochCalcK2

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt StochCalcTiltM
  StochCalcSteinM StochCalcStein StochCalcOrth

section generic

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}


end generic

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]







end StochCalcK2
/-! K2c (8c066573 relay 2): Bessel inequality for two orthogonal test variables, and the
`Z_T`-weighted martingale-difference sums `S = Σ_{k<N} Y_k ξ_k` on the grid `gr p n`
(`E_P[Z_T² S²] = Σ E_P[Z_T² Y_k²] T/n`, `E_P[Z_T² S] = E_P[Z_T S] = 0`) via the auxiliary
measure `Q2 = (Z_T²/c)·P`, under which the grid increments keep their independence and laws.
Append after K2b_tail.lean (needs D2_tail's `gr`, `V_gr`; i.e. a dev file containing D2). -/

namespace StochCalcK2

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt StochCalcTiltM
  StochCalcSteinM StochCalcP6S

section generic

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]



end generic

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]




















end StochCalcK2


/-! O7Q2 (8c066573 relay 34, O7.5 glue hQb): Bayes formula for the tilted measure
`Q = (Z²/c)·P` and the Q2 form of O7.4: with `g = θ / Z_T`,
`E_Q[g | m] = E_P[θ|F_t] / Z_t` for every `F_t ≤ m ≤ F_t ⊔ G_T`; hence
`E_Q[g | F_t ⊔ G_T] = E_Q[g | F_t]` (the `hQb` hypothesis of `StochCalcE2.E2_bound`).
Generic: `StochCalcQ2.bayes_ce`.  Model: `StochCalcQ2.Q2ce`, `StochCalcQ2.Q2_hQb`.
Append after O7Q1M_tail (inside the dev file's `namespace StochCalcP6`). -/

namespace StochCalcQ2

open MeasureTheory ProbabilityTheory Filter Topology
open StochCalcTilt
open scoped NNReal ENNReal

section generic

variable {Ω : Type*} {m mH : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]


end generic

end StochCalcQ2

namespace StochCalcQ2M

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW StochCalcZ2 StochCalcZ3 StochCalcZ4m StochCalcZ4mb StochCalcHit
open StochCalcO3 StochCalcO3M StochCalcZ7a StochCalcZ7b StochCalcZ7d StochCalcCE StochCalcR1M
open StochCalcZK StochCalcKF StochCalcTilt StochCalcQ2
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]



end StochCalcQ2M


/-! O7.5 piece (relay 21): one-cell identity of the E2 error argument (pure Mathlib).
F-filtration (F k) ≤ (F (k + 1)), enlarged H-filtration (H k) ≤ (H (k + 1)) ((F k) ≤ (H k), (F (k + 1)) ≤ (H (k + 1))), increment w ((F (k + 1))-measurable,
"independent of (H k) with mean 0" in the form `hind`), g with E[g|(H (k + 1))] = E[g|(F (k + 1))] (Q1), NC for (F k)-multipliers.
Then for a bounded (H k)-measurable y:  E[g y w] = E[(gb - ga) w (yb - ya)]. -/

set_option autoImplicit false

open MeasureTheory Filter
open scoped NNReal

namespace StochCalcE2

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]



end StochCalcE2

-- O7E3 tail (8c066573 relay 24): append after lib/stochcalc/O7E2.lean (pure Mathlib).

/-! O7.5 (E2 n-cell sum): splitting a cell into `n` pieces, the NC orthogonality gives
`|E[g y ΣΔW]| ≤ l/2 E g² + (1/2l)(μ/2 Σ E w_k⁴ + 2 Cy⁴/μ)` for all `l, μ > 0`; with `Σ E w_k⁴ = O(1/n)`
this forces `E[g y ΣΔW] = 0`. -/

namespace StochCalcE2

open MeasureTheory Filter Topology
open scoped NNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]









end StochCalcE2


/-! O7G4 (8c066573 relay 24, for the O7.5 model instance): fourth moments of centred Gaussians
scale like `v²`: `∫ x⁴ dN(0,v) = v² ∫ x⁴ dN(0,1)`, and a random variable with law `N(0,v)` has
`E w⁴ = v² K₄`, `K₄ := ∫ x⁴ dN(0,1)` (finite). Pure Mathlib. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace StochCalcG4




end StochCalcG4

/-! O7E5 (8c066573 relay 34, O7.5 model glue): under `Q2 = (Z_T²/c)·P`, if `g = f/Z_T` has the
Q1 property `E_Q2[g | F_t ⊔ G_T] = E_Q2[g | F_t]` (`StochCalcQ2M.Q2ce`) and `f` is orthogonal to
the grid class `NC` (expanded form `hfN`), then `E_Q2[g y (B~_{t_{j+1}} - B~_{t_j})] = 0` for every
bounded `F_{t_j} ⊔ G_T`-measurable `y` (cell split in `r` pieces + `StochCalcE2.E2_bound` +
`StochCalcE2.zero_of_bounds`).  Append after E2G4_block (dev base M15). -/

namespace StochCalcE5M

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV
open StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt StochCalcTiltM StochCalcSteinM StochCalcP6S
open StochCalcK2 StochCalcD2 StochCalcE2 StochCalcG4
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]




end StochCalcE5M

end StochCalcP6
-- ===== slice of RUmod (scratch/probe/slice8c/cuts/r_l2.lean.src/RUmod.lean): 11/17 top-level decls kept =====

namespace StochCalcP6

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

/-! RU (8c066573 relay 44): Elem-free ("unpacked") forms of `Rep`, `closure (range eL)`, `closure (range TL)`
and `IncrHyp`, so that cut statements become Definitions-only after unfolding. -/

namespace StochCalcRU

open StochCalcO3
open scoped InnerProductSpace RealInnerProductSpace

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}

/-- Elementary time-space functions `1_[u,v) Y`, Elem-free. -/
def SE (m : ℝ≥0 → MeasurableSpace Ω) (P : Measure Ω) (T : ℝ≥0) : Set (Lp ℝ 2 (μT P T)) :=
  {g | ∃ u v : ℝ≥0, u ≤ v ∧ v ≤ T ∧ ∃ Y : Ω → ℝ, Measurable[m u] Y ∧ (∃ C : ℝ, ∀ ω, |Y ω| ≤ C) ∧
    ∃ h : MemLp (fun z : ℝ × Ω => ind u v z.1 * Y z.2) 2 (μT P T), g = h.toLp _}

/-- Elementary stochastic integrals `Y (W_v - W_u)`, Elem-free. -/
def SI (m : ℝ≥0 → MeasurableSpace Ω) (W : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (T : ℝ≥0) : Set (Lp ℝ 2 P) :=
  {g | ∃ u v : ℝ≥0, u ≤ v ∧ v ≤ T ∧ ∃ Y : Ω → ℝ, Measurable[m u] Y ∧ (∃ C : ℝ, ∀ ω, |Y ω| ≤ C) ∧
    ∃ h : MemLp (fun ω => Y ω * (W v ω - W u ω)) 2 P, g = h.toLp _}

/-- `Rep`, Elem-free. -/
def RepU (m : ℝ≥0 → MeasurableSpace Ω) (W : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (T : ℝ≥0)
    (θ : Lp ℝ 2 P) (b : Lp ℝ 2 (μT P T)) : Prop :=
  θ ∈ closure (Submodule.span ℝ (SI m W P T) : Set (Lp ℝ 2 P)) ∧
    b ∈ closure (Submodule.span ℝ (SE m P T) : Set (Lp ℝ 2 (μT P T))) ∧
    ∀ u v : ℝ≥0, u ≤ v → v ≤ T → ∀ Y : Ω → ℝ, Measurable[m u] Y → (∃ C : ℝ, ∀ ω, |Y ω| ≤ C) →
      ∫ ω, (θ : Ω → ℝ) ω * (Y ω * (W v ω - W u ω)) ∂P =
        ∫ z, (b : ℝ × Ω → ℝ) z * (ind u v z.1 * Y z.2) ∂(μT P T)



lemma range_eE (hle : ∀ t, m t ≤ mΩ) (T : ℝ≥0) :
    Set.range (eE (P := P) hle T) = SE m P T := by
  ext g
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i.u, i.v, i.huv, i.hvT, i.Y, i.hY, ⟨i.C, i.hC⟩, memLp_efun hle i, rfl⟩
  · rintro ⟨u, v, huv, hvT, Y, hY, ⟨C, hC⟩, h, rfl⟩
    exact ⟨⟨u, v, huv, hvT, Y, hY, C, hC⟩, rfl⟩

lemma range_eI (hW : IncrHyp m W P) (T : ℝ≥0) :
    Set.range (eI hW T) = SI m W P T := by
  ext g
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i.u, i.v, i.huv, i.hvT, i.Y, i.hY, ⟨i.C, i.hC⟩, memLp_ifun hW i, rfl⟩
  · rintro ⟨u, v, huv, hvT, Y, hY, ⟨C, hC⟩, h, rfl⟩
    exact ⟨⟨u, v, huv, hvT, Y, hY, C, hC⟩, rfl⟩

lemma range_eL (hle : ∀ t, m t ≤ mΩ) (T : ℝ≥0) :
    Set.range (eL (P := P) hle T) = (Submodule.span ℝ (SE m P T) : Set (Lp ℝ 2 (μT P T))) := by
  rw [← LinearMap.coe_range]
  unfold eL
  rw [Finsupp.range_linearCombination, range_eE]

lemma range_TL (hW : IncrHyp m W P) (T : ℝ≥0) :
    Set.range (TL hW T) = (Submodule.span ℝ (SI m W P T) : Set (Lp ℝ 2 P)) := by
  rw [← LinearMap.coe_range]
  unfold TL
  rw [Finsupp.range_linearCombination, range_eI]

lemma closure_eL (hle : ∀ t, m t ≤ mΩ) (T : ℝ≥0) :
    closure (Set.range (eL (P := P) hle T)) =
      closure (Submodule.span ℝ (SE m P T) : Set (Lp ℝ 2 (μT P T))) := by
  rw [range_eL]

lemma int_eI (hW : IncrHyp m W P) {T : ℝ≥0} (θ : Lp ℝ 2 P) (i : Elem m T) :
    ∫ ω, (θ : Ω → ℝ) ω * (i.Y ω * (W i.v ω - W i.u ω)) ∂P = ⟪θ, eI hW T i⟫_ℝ := by
  unfold eI
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_ifun hW i).coeFn_toLp] with ω hω
  rw [hω, ifun, RCLike.inner_apply, conj_trivial, mul_comm]

lemma int_eE (hle : ∀ t, m t ≤ mΩ) {T : ℝ≥0} (b : Lp ℝ 2 (μT P T)) (i : Elem m T) :
    ∫ z, (b : ℝ × Ω → ℝ) z * (ind i.u i.v z.1 * i.Y z.2) ∂(μT P T) = ⟪b, eE (P := P) hle T i⟫_ℝ := by
  unfold eE
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_efun (P := P) hle i).coeFn_toLp] with z hz
  rw [hz, efun, RCLike.inner_apply, conj_trivial, mul_comm]

lemma rep_iff (hW : IncrHyp m W P) (T : ℝ≥0) (θ : Lp ℝ 2 P) (b : Lp ℝ 2 (μT P T)) :
    StochCalcO3.Rep hW T θ b ↔ RepU m W P T θ b := by
  unfold StochCalcO3.Rep RepU
  rw [range_TL, range_eL]
  refine and_congr Iff.rfl (and_congr Iff.rfl ⟨fun h => ?_, fun h => ?_⟩)
  · intro u v huv hvT Y hY hC
    obtain ⟨C, hC⟩ := hC
    let i : Elem m T := ⟨u, v, huv, hvT, Y, hY, C, hC⟩
    have h1 := h (Finsupp.single i 1)
    simp only [TL, eL, Finsupp.linearCombination_single, one_smul] at h1
    rw [int_eI hW θ i, int_eE hW.le b i]
    exact h1
  · intro x
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add s1 s2 h1 h2 => simp only [map_add, inner_add_right, h1, h2]
    | single i a =>
      simp only [TL, eL, Finsupp.linearCombination_single, real_inner_smul_right]
      rw [← int_eI hW θ i, ← int_eE hW.le b i, h i.u i.v i.huv i.hvT i.Y i.hY ⟨i.C, i.hC⟩]

end StochCalcRU

namespace StochCalcQ2U

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcZ2 StochCalcZ3 StochCalcO3
open StochCalcZK
open StochCalcRU
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]





end StochCalcQ2U

end StochCalcP6

-- ===== slice of P8c066573M16c (scratch/probe/slice8c/cuts/r_l2.lean.src/P8c066573M16c.lean): 56/865 top-level decls kept =====

/-! Bridge from the HedgePSNV model to the ItoLib library (Solutions/Sol_pv_1558a108.lean):
a standard 2-d Brownian motion `W = (B, B~)` (modified on a null set so that every path is
continuous), with `F t ≤ completedBrownianPast P W 0 t`, and the transfer of
`HasBrownianItoIntegral` from `(F, B)` / `(F, B~)` to `(cBP, W · · 0)` / `(cBP, W · · 1)`. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace StochCalcBr

open HedgePSNV EthierKurtz

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]



































end StochCalcBr

/-! D1a (pathwise half): if an Ito integral `I` equals `-(1/2) ∫_0^· g` at all dyadic grid points
(`g = η²` continuous) and its quadratic-variation sums converge in measure to `∫_0^T g`
(ItoLib.qvJ_tendsto with `B := 1`, `H1 = H2 = η`), then `∫_0^T g = 0` a.s.
The QV sums of a continuous finite-variation path vanish: `∑ (∫_cell g)^2 ≤ M^2 T^2 / 2^n`. -/

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped NNReal ENNReal BigOperators

namespace StochCalcD1a

variable {Ω : Type*} [MeasurableSpace Ω]






end StochCalcD1a

/-! D1a wiring (relay 6): in the degenerate case `Z_T = 1` a.s., the drift `μ` vanishes
`dt`-a.e. on `[0,T]`, so `X_t = x₀ + J_t` for `t ≤ T`. The quadratic-variation input is the
hypothesis `hQV` = statement of the planned platform child C_QV (ItoLib.qvJ_tendsto with
`B := 1`, `j = j'`, `H1 = H2`). -/

namespace StochCalcD1aW

open HedgePSNV EthierKurtz StochCalcBr

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]










end StochCalcD1aW

/-! LA / D1b (relay 6 start): an Ito integral `J = ∫ H dW^j` of a continuous adapted integrand with
`E ∫_0^T H² < ∞` (and a.s. continuous paths on `[0,T]`) is square integrable and satisfies the
martingale property in set-integral form for every `A ∈ completedBrownianPast s`, `A` measurable.
(`completedBrownianPast` contains non-measurable null subsets, so `condExp` wrt it is junk;
the model side converts the set-integral form into `IsMartingaleOn` for `F`.)
Dev file: imports the accepted ItoLib (Sol_pv_1558a108); the platform child pastes the prefix. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter EthierKurtz
open scoped NNReal ENNReal Topology BigOperators

namespace StochCalcL2M

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}










/-! Lemma B (relay 7): martingale property of the Ito integral of a BOUNDED continuous adapted
integrand at dyadic grid times, set-integral form. -/





/-! Lemma C (relay 7): unbounded continuous adapted integrands with `E ∫_0^t H² < ∞`. -/






/-! Lemma D (relay 7): `L²` bound and martingale property at arbitrary times `s ≤ t`. -/



end StochCalcL2M

/-! D1b (relay 7): the model's `dB`-integral `J = ∫ Xσ dB` is a `P`-martingale on `[0,T]` (set-integral
form for `F`), and in the degenerate case `Z_T = 1` the price `X` is a `P`-martingale on `[0,T]`. -/

namespace StochCalcD1b

open HedgePSNV EthierKurtz StochCalcBr StochCalcL2M ItoLib

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]












end StochCalcD1b

/-! P1 for D2 (relay 7): the future increments of one Brownian coordinate `j` after `t₀` are
independent of the joint family {all coordinates up to `t₀`} ∪ {the other coordinates at all
times}. Used for the exponential tilts `Q_λ ∈ M_X` (D2) and Gaussian integration by parts. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter EthierKurtz
open scoped NNReal ENNReal Topology

namespace StochCalcIndep

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}




end StochCalcIndep

/-! P1b (relay 7): the model σ-algebras `F_c ⊔ G_T'` sit inside the a.e. closure of the
past-of-`B~`/all-of-`B` σ-algebra of the library Brownian motion `W M`; hence the `B~`
increments after `c` are independent of `F_c ⊔ G_T'`. -/

namespace StochCalcHs

open HedgePSNV EthierKurtz StochCalcBr StochCalcIndep ItoLib

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]








end StochCalcHs

/-! P2 for D2 (relay 8): Gaussian facts for a centred Gaussian `ξ ~ N(0, v)`:
exponential moments, the tilt `L c = exp(c ξ - v c²/2)` (mean one, in L²), and the
derivative-at-zero limit `E[ξ Y] = 0` from `E[(L c - 1) Y] = 0` for small `c ≠ 0` (DCT). -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace StochCalcGauss

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ξ : Ω → ℝ} {v : ℝ≥0}


















end StochCalcGauss

/-! P3 generic part (relay 8): change of measure by a positive mean-one L² density `D`,
set integrals / integrability under `Q = P.withDensity (ofReal ∘ D)`, the martingale property
under `Q` from set-integral identities under `P`, and the one-step tilt identity
`∫_A E R X_v = ∫_A E R X_s` (E `𝓕`-measurable, R independent of `𝓗 ⊇ 𝓕`, mean one). -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace StochCalcTilt

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]












end StochCalcTilt
/-! P3 model part (relay 8): the exponential `B~`-increment tilts
`Q_c = P.withDensity (exp(c (B~_{t'} - B~_t) - c²(t'-t)/2))` belong to `M_X` whenever `X` is an
L² `P`-martingale on `[0, T]` (degenerate case). -/

namespace StochCalcTiltM

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]



















end StochCalcTiltM
/-! P4 (relay 8): every admissible gains process is orthogonal to the future `B~` increments:
`E[Y ξ χ_T] = 0` for `ξ = B~_{t'} - B~_t` and bounded `F_t`-measurable `Y` (degenerate case,
`X` an L² `P`-martingale), via the tilts `Q_c ∈ M_X` and `d/dc|₀`. -/

namespace StochCalcOrth

open HedgePSNV EthierKurtz StochCalcBr StochCalcGauss StochCalcTilt StochCalcTiltM

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]





end StochCalcOrth

/-! P5 for D2 (relay 9): Gaussian integration by parts (Stein) for the hinge
`x ↦ max (k - s x) 0`, and its independent-conditioning form
`E[ξ (k0 - a (R - (U + s ξ))^+) Y] = a s v E[Y 1{U + s ξ ≤ R}]` for `ξ ~ N(0, v)` independent of `(U, Y)`. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace StochCalcStein








end StochCalcStein
/-! P5 model part (relay 9): Stein identity for the production payoff against a `B~` increment:
`E[ξ H Y] = (P - s) σ~ (t' - t) E[Y 1{A_T ≤ R}]` for `ξ = B~_{t'} - B~_t` and bounded `F_t`-measurable `Y`
(no degeneracy needed: `ξ` is independent of `F_t ⊔ G_T ⊔ σ(B~_T - B~_{t'})`). -/

namespace StochCalcSteinM

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcTiltM StochCalcStein

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]






end StochCalcSteinM

/-! P6 generic pieces (relay 9): (A) a variance lower bound from a test variable `D` with
`E D = 0` and `E[D U] = E[D²]`; (B) left Riemann sums of a monotone function on a uniform grid. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace StochCalcP6




/-! P6 generic (relay 10): martingale-difference sums `S n = Σ_{k<n} Y k * ξ k` with `ξ k`
independent of `m k`, centred, in `L²`, `m (k+1)`-measurable, and `Y k` bounded `m k`-measurable:
`E S = 0`, `S ∈ L²`, `E S² = Σ E[Y k²] E[ξ k²]`. Plus Gaussian moments. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace StochCalcP6S

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]




variable (m : ℕ → MeasurableSpace Ω) (ξ Y : ℕ → Ω → ℝ)



end StochCalcP6S

/-! Degenerate case `Z_T = 1` a.s. of Theorem 1(ii) (child `HedgePSNV.theorem_1_ii_degenerate` of
proposition_5 cc6d45ce): reduction of the child to three stochastic obligations
  (D1) `X` is a `P`-martingale on `[0,T]`,
  (D2) lower bound `Psi ≤ Var[H + χ_T]` for every admissible strategy,
  (D3) approximate attainment `∃ (θ,χ) ∈ A_X, Var[H + χ_T] ≤ Psi + ε`,
plus the elementary degenerate facts (`P^M = P`, `Z_t = Z^M_t = 1` a.s., `E χ_T = 0`). -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace StochCalcHedgeDeg

open HedgePSNV

variable {p : Params} {Ω : Type*} [MeasurableSpace Ω]











end StochCalcHedgeDeg

/-! D2 (relay 10): the degenerate lower bound `Psi ≤ Var[H + χ_T]` for every admissible strategy,
via the test variables `D_n = Σ_k σ~(P-s) c_{t_k} ξ_k` (P4 orthogonality, P5 Stein, P6 Riemann sums). -/

namespace StochCalcD2

open HedgePSNV StochCalcBr StochCalcTiltM StochCalcSteinM StochCalcOrth StochCalcHedgeDeg StochCalcGauss

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]




















end StochCalcD2

/-! D2 limit (relay 10): Riemann sums of the monotone `u ↦ E[δ_u²]` and `Psi_deg`. -/

namespace StochCalcD2

open HedgePSNV StochCalcBr StochCalcTiltM StochCalcHedgeDeg

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]









end StochCalcD2
/-! D3 reduction (relay 11): approximate attainment `Var[H + χ_T] ≤ Psi + ε` from ONE
L²-density statement (`hdens` of `StochCalcD3.D3_of_density`): for every `η > 0` some
admissible `χ`, constant `c` and simple `dB̃`-sum `K = Σ Z_k ξ_k` on a uniform grid have
`E[(H + χ_T − c − K)²] ≤ η`.  Proof: `D = Σ σ̃(P−s) Yc_{t_k} ξ_k` is the projection of
`U = H + χ_T − c` onto the simple `dB̃`-sums of the grid (Stein + polarized isometry), so
`E U² ≤ E D² + E (U − K)²`, and `E D²` is a left Riemann sum of the monotone `u ↦ E δ_u²`. -/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace StochCalcP6




end StochCalcP6

namespace StochCalcP6S

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable (m : ℕ → MeasurableSpace Ω) (ξ : ℕ → Ω → ℝ)


end StochCalcP6S

namespace StochCalcD3

open HedgePSNV StochCalcBr StochCalcTiltM StochCalcSteinM StochCalcOrth StochCalcHedgeDeg
  StochCalcGauss StochCalcD2

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]



end StochCalcD3
/-! D3 split (relay 11): `hdens` of `D3_of_density` from
  (R)  representation density: `H ≈ c + Σ Y_k ΔB_k + Σ Z_k ΔB̃_k` in L² on a uniform grid;
  (XS) hedging of a simple `dB`-sum by an admissible strategy: `χ_T ≈ −Σ Y_k ΔB_k` in L².
Grid refinement `n → n*m` is exact (telescoping). -/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace StochCalcD3

open HedgePSNV StochCalcBr StochCalcTiltM StochCalcSteinM StochCalcOrth StochCalcHedgeDeg
  StochCalcGauss StochCalcD2

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]








end StochCalcD3

/-! R1 generic (relay 13): telescoping-product approximation of `exp (i Σ x_k)` by a constant
plus an adapted "stochastic sum" `Σ A_k (i x_k)`, for a discrete filtration `m` and increments
`x k` that are `m (k+1)`-measurable, independent of `m k`, centred, with `E x_k⁴ ≤ D`.
Error in `L²`: `≤ 16 n D`.  Mathlib only. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Finset
open scoped NNReal ENNReal

namespace StochCalcR1



variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]









end StochCalcR1

/-! R1 model (relay 13): `exp (i Σ_k (λ_k ΔB_k + μ_k ΔB~_k))` on a uniform grid is `L²`-close to a
constant plus an adapted fine-grid sum `Σ_l A_l · i (a_l ΔB_l + b_l ΔB~_l)`.  Needs the joint
independence of `(ΔB, ΔB~)` on `[u, w]` from `F_u` (new: `indep_B_incr`, `indep_pair`). -/

namespace StochCalcR1M

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcIndep ItoLib StochCalcTiltM
  StochCalcSteinM StochCalcStein StochCalcD2 StochCalcD3 StochCalcGauss StochCalcP6S Finset

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]






















end StochCalcR1M

/-! R4 (relay 13): the class `IsGS` of grid sums `c + Σ Y_k ΔB_k + Σ Z_k ΔB~_k` (bounded adapted
coefficients on a uniform grid) is a vector space of `F_T`-measurable `L²` functions. -/

namespace StochCalcR4

open HedgePSNV StochCalcTiltM StochCalcD2 StochCalcD3 StochCalcGauss Finset

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]







end StochCalcR4

/-! R2a (relay 12): characteristic-function identification.  If an integrable `V` is orthogonal to
`cos ⟪Δ, t⟫` and `sin ⟪Δ, t⟫` for every `t`, then `∫_A V = 0` for every `A ∈ σ(Δ)`.
Mathlib only. -/

open MeasureTheory ProbabilityTheory Complex
open scoped ENNReal

namespace StochCalcR2

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E] [mE : MeasurableSpace E] [BorelSpace E]



end StochCalcR2

/-! R2b (relay 12): π-λ extension of vanishing set integrals from an increasing sequence of
σ-algebras to their supremum joined with the `P`-null sets, and the a.e.-limit criterion that
puts a variable's σ-algebra below it.  Mathlib only. -/

open MeasureTheory Filter
open scoped ENNReal Topology

namespace StochCalcR2








end StochCalcR2

/-! R2c (relay 12): the generic identification theorem. -/

namespace StochCalcR2

open MeasureTheory


end StochCalcR2

/-! R3 (relay 12): Hilbert-space glue.  A subspace (given as a predicate on functions) of `L²`
whose orthogonal complement is trivial is `L²`-dense.  Mathlib only. -/

open MeasureTheory Filter
open scoped ENNReal

namespace StochCalcR3


end StochCalcR3

/-! R6 generic (relay 13): orthogonality passes to `L²`-limits.  Mathlib only. -/

set_option autoImplicit false

open MeasureTheory

namespace StochCalcR6



end StochCalcR6

/-! R5 (relay 14): the grid-`2^j` increment vectors `Δ_j` of `(B, B~)`, the monotonicity of
their σ-algebras, `F_T ≤ aug (⨆ σ(Δ_j))`, and `⟪Δ_j, t⟫` as a grid sum. -/

namespace StochCalcR5

open HedgePSNV StochCalcTiltM StochCalcD2 StochCalcD3 StochCalcR4 StochCalcR2 Finset Filter
open scoped Topology



variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]





















end StochCalcR5

/-! R7 (relay 14): trigonometric functions of `Δ_j` are `L²`-limits of grid sums; hence the
grid sums are dense in `L²(F_T)` (hsep + R3), which is the hypothesis `hR` of `dens_of_rep`. -/

namespace StochCalcR7

open HedgePSNV StochCalcTiltM StochCalcD2 StochCalcD3 StochCalcR4 StochCalcR5 StochCalcR1M
  Finset Filter




variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]









end StochCalcR7

/-! TC (relay 15 of cc6d45ce): truncation consistency of the Ito integral at an ARBITRARY time
`r ≤ t`.  The clamped left-point sums of the horizon-`t` dyadic grid, masked to the cells that
start before `r`, converge in probability to `J r`, given that `J` is continuous in probability
along the dyadic floors `r_n ↑ r`.  Three-term argument: dyadic floor `r_n` (ItoLib M7a
`partialSum_tendsto_of_hasBrownianItoIntegral`), the cells in `[r_n, r)` (Lenglart bound
`itoStepSum_local_chebyshev`, at most `2^m` cells of length `t/2^(n+m)`), and `J r_n → J r`.
Use: hXS step S1 (Ito integral of a simple-in-time strategy times `Xσ`). -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter EthierKurtz
open scoped NNReal ENNReal Topology BigOperators

namespace StochCalcTC

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}
















/-! S1b preparation (relay 15): one cell for every coefficient family; `thetaS` bounds. -/





end StochCalcTC

/-! TC2 (relay 16 of cc6d45ce): S1b, the integrated-squared-error clause for the
`thetaS · clamp_N H` approximants. -/

namespace StochCalcTC

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]








end StochCalcTC

/-! TC3 (relay 16 of cc6d45ce): S1 assembly.  The Ito integral of the simple-in-time weight
`thetaS s θ n'` times a continuous adapted `H` is `Σ_i θ_i (J(s_{i+1} ∧ t) − J(s_i ∧ t))`. -/

namespace StochCalcTC

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}





end StochCalcTC

/-! TC4 (relay 16 of cc6d45ce): variant of S1c needing `J`-continuity only at the jump times;
dyadic floors converge; clause 1 of the Ito relation for `thetaS · H`. -/

namespace StochCalcTC

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}





end StochCalcTC

/-! Mart (relay 16 of cc6d45ce): simple stochastic integrals of a martingale are martingales.
`θ (X(b ∧ t) − X(a ∧ t))` with `θ` bounded `F a`-measurable is an `IsMartingaleOn` martingale;
finite sums too.  Generic (any filtration, any finite measure). -/

set_option autoImplicit false

open MeasureTheory Filter
open scoped NNReal

namespace StochCalcMart

open HedgePSNV

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]






end StochCalcMart

/-! S1M (relay 16 of cc6d45ce): in the degenerate model, a simple-in-time strategy
`thetaS s θ n'` (jump times `s_i ≤ T`, `θ_i` bounded `F(s_i)`-measurable) with gains
`chiS = Σ θ_i (X(s_{i+1} ∧ t) − X(s_i ∧ t))` is admissible: `(thetaS, chiS) ∈ A_X`. -/

namespace StochCalcS1M

open HedgePSNV EthierKurtz StochCalcBr StochCalcD1b StochCalcD1aW StochCalcTC StochCalcMart ItoLib

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]











end StochCalcS1M

/-! TCR (8c066573 relay 15, O2 core): truncation consistency at a RANDOM cutoff `ρ ≤ t` that is a
stopping time of the completed Brownian past.  Same three-term argument as `truncSum_tendsto`,
with the dyadic CEILING `ρ^n = dyTime t n ⌈ρ/t·2^n⌉` (a stopping time, finitely many values):
masked sums up to `ρ^n` are finitely many deterministic truncations (`trunc_dy_tendsto`), the
cells in `[ρ, ρ^n)` are adapted (Lenglart), and `J (ρ^n) → J ρ` is a hypothesis. -/

namespace StochCalcTC

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}











end StochCalcTC

/-! S1b with RANDOM jump times `s ω` (8c066573 relay 15): the argument is pathwise. -/

namespace StochCalcTC

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}



end StochCalcTC

/-! S1RM (8c066573 relay 15, O2b): the Ito relation for a STOPPED simple strategy
`θ = Y 1{s∧τ ≤ u < s'∧τ}` in the model, with `K_t = Y (J(s'∧τ∧t) − J(s∧τ∧t))`.
Append after probe/cc6d45ce_S1M.lean + lib/stochcalc/TCR_tail.lean + lib/stochcalc/S1bR_tail.lean.
Hypothesis `hJc` (J along dyadic ceilings of a random time) is discharged separately (needs s' < T). -/

namespace StochCalcS1R

open HedgePSNV EthierKurtz StochCalcBr StochCalcD1b StochCalcD1aW StochCalcTC StochCalcMart
  StochCalcS1M ItoLib

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]









end StochCalcS1R
/-! S1RJ (8c066573 relay 16, O2c): discharge `hJc` of `S1R_model` for random times bounded by
`s' < T`, giving `S1R_modelT` (no `hJc` hypothesis).
Append after probe/8c066573_S1R.lean (= cc6d45ce_S1M + TCR_tail + S1bR_tail + S1RM_tail). -/

namespace StochCalcS1R

open HedgePSNV EthierKurtz StochCalcBr StochCalcD1b StochCalcD1aW StochCalcTC StochCalcMart
  StochCalcS1M ItoLib

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]






end StochCalcS1R

/-! OS (8c066573 relay 14): continuous-time optional stopping for `IsMartingaleOn`.
A continuous martingale on `[0,T]` stopped at a stopping time is again a martingale on `[0,T]`.
Proof: grid stopping times `jn` on `s + k (t-s)/(N+1)` (Mathlib discrete optional sampling gives
`X(grid ceiling of ρ) = E[X t | F_ρN]`), uniform integrability of conditional expectations,
pointwise convergence by path continuity, Vitali.  Generic (any filtration, finite measure). -/

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace StochCalcOS

open HedgePSNV

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]



























end StochCalcOS

/-! Hit (8c066573 relay 16, O2a): the hitting time of the closed set `{R ≤ |x|}` by a process
with continuous paths, capped at `T`, is a stopping time of any filtration to which the
process is adapted (no right-continuity of the filtration needed: closed set + continuous paths).
Also: the stopped process is bounded by `R` when it starts inside. Mathlib only. -/

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace StochCalcHit

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]











end StochCalcHit
/-! S1RA (8c066573 relay 16, O2d): the stopped simple strategy
`θ = Y 1{s∧τ ≤ u < s'∧τ}`, `χ_t = Y (X_{s'∧τ∧t} − X_{s∧τ∧t})` is admissible (`∈ M.AX`) when
`s ≤ s' < T`, `τ` is a stopping time and the stopped price is bounded (e.g. `τ = hitR`).
Append after probe/8c066573_S1RJ.lean + the body of lib/stochcalc/Hit.lean (no import line). -/

namespace StochCalcS1R

open HedgePSNV EthierKurtz StochCalcBr StochCalcD1b StochCalcD1aW StochCalcTC StochCalcMart
  StochCalcS1M ItoLib StochCalcOS StochCalcHit

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]











end StochCalcS1R

/-! RieszIso (8c066573 relay 16, O3 core): if a linear map `T : S → F` into a Hilbert space is
isometric for a seminorm given by a linear map `e : S → E` into another Hilbert space
(`‖T s‖ = ‖e s‖`), then every `f ∈ F` has a "representing integrand" `a ∈ E` with
`⟪f, T s⟫ = ⟪a, e s⟫` for all `s`.  (Use: `S` = simple adapted processes, `e` = their class in
`L²(dt ⊗ dP)`, `T` = the elementary stochastic integral into `L²(P)`.)  Mathlib only; no quotient
by null processes is needed. -/

set_option autoImplicit false

open Filter Topology
open scoped InnerProductSpace RealInnerProductSpace

namespace StochCalcRiesz

variable {S E F : Type*} [AddCommGroup S] [Module ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]




end StochCalcRiesz

/-! O3gen (8c066573 relay 17, O3 instantiation, generic; append after RieszIso.lean, Mathlib only).
For a real process `W` with independent centred increments of variance `v - u` w.r.t. a monotone family
`m t` of σ-algebras, every `f ∈ L²(P)` has a representing integrand `a ∈ L²(dt|[0,T] ⊗ P)` (in the closure of
the adapted simple processes) with `E[f · Y (W_v - W_u)] = ∫∫ a · 1_[u,v) Y` for all bounded `m u`-measurable `Y`. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]


variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}
































end StochCalcO3

/-! O3M (8c066573 relay 17, O3 model instantiation): `B` and `B~` satisfy `StochCalcO3.IncrHyp` w.r.t. `M.F`,
so every `f ∈ L²(P)` has representing integrands `a, b ∈ L²(dt|[0,T) ⊗ P)` (in the closure of adapted simple processes):
`E[f Y (B_v - B_u)] = ∫∫ a 1_[u,v) Y` and `E[f Y (B~_v - B~_u)] = ∫∫ b 1_[u,v) Y`.
Append after probe/8c066573_S1RA.lean + RieszIso.lean body + O3gen_tail.lean (no import lines). -/

namespace StochCalcO3M

open HedgePSNV StochCalcBr StochCalcO3 StochCalcD3 StochCalcR1M StochCalcTiltM StochCalcSteinM
  StochCalcGauss StochCalcP6S

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]





end StochCalcO3M

/-! O4gen (8c066573 relay 17, O4 generic part; append after O3gen_tail.lean, Mathlib only).
If elementary combinations `s n` have time-space classes `eL (s n) → ψ` in `L²(μT)` and elementary integrals
`TL (s n) → J` in measure, then `J` has an `L²` version `K` with `‖K‖ = ‖ψ‖` (isometry) and `⟪f, K⟫ = ⟪a, ψ⟫`
for the representing integrand `a` of `f` (O3).  Plus pointwise formulas `coe_TL` / `coe_eL` for combinations. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}





end StochCalcO3

/-! O4step (8c066573 relay 18, O4 generic step-approximation part).  Append after O4gen_tail.lean.
Needs `Definitions.Def_EthierKurtz_itoStepValue`, `Definitions.Def_EthierKurtz_itoStepSum` and
`Solutions.Sol_pv_1558a108` (ItoLib) imported.
`O4fun`: function form of O4gen.  `O4step`: given EK approximants `a0` of a BOUNDED jointly measurable
integrand `H` (integrated squared error → 0 in probability, step sums → `J` in probability) and the ItoLib
"zero lemma" for step sums, the approximants clamped at the bound of `H` are elementary combinations whose
time-space classes converge to `H` in `L²(μT)` and whose integrals still converge to `J`; hence
`∫ f J dP = ∫ a H dμT` for the representing integrand `a` of `f` (O3). -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology EthierKurtz ItoLib
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}



/-! Clamping and step values. -/








/-! The clamped approximants as elementary combinations. -/











end StochCalcO3

/-! O4 model (8c066573 relay 18; append after O4step_tail.lean in the model dev file).
The doubly stopped simple strategy `θ = Y 1{s∧τ ≤ u < s'∧τ}`, `τ = hitR X R ∧ hitR σ R'`, is admissible
(`dblSimple_mem_AX`) and its Itô integrand `θ X σ` is bounded by `C R R'`, so `O4step` gives
`E[f · Y (J_{s'∧τ} - J_{s∧τ})] = ∫ a θ X σ dμT` for the representing integrand `a` of `f` (O3, dB part). -/

namespace StochCalcO4M

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1b StochCalcO3 StochCalcO3M StochCalcS1R StochCalcHit
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]











end StochCalcO4M
/-! O5 drift identity (8c066573 relay 19; append after O4M_tail.lean in the model dev file).
Triple stop `τ = hitR X R ∧ hitR σ R' ∧ hitR μ R''` bounds both integrands `θ X σ` and `θ X μ`.
KEY (relay 19): no conditional expectation `f_u` is needed for the drift: Fubini alone gives
`E[f ∫_0^T θ X μ du] = ∫ (θ X μ)(u,ω) f(ω) dμT`.  With O4 and `f ⊥ χ_T`:
`O5_gain : ∫ a θ X σ dμT + ∫ θ X μ f dμT = 0` for every triple-stopped simple strategy. -/

namespace StochCalcO5

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1b StochCalcO3 StochCalcO3M StochCalcS1R StochCalcHit StochCalcO4M
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]










end StochCalcO5
/-! O6a (8c066573 relay 19): Pred-membership of bounded step-approximable integrands.
Append after O56_tail.lean.  `pred_approx` = the L²(μT) half of O4step (no stochastic integral):
any bounded jointly measurable `H` whose dyadic step approximants `a0` (adapted, NOT necessarily
bounded) have integrated squared error → 0 in probability is an `L²(μT)` limit of elementary
combinations; `pred_mem` states it as membership of the class of `H` in the closure of `range eL`. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology EthierKurtz ItoLib
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω}



end StochCalcO3

/-! O6b (8c066573 relay 20): left-point sampling.  Append after O6a_tail.lean.
`pred_left`: a bounded, jointly measurable, adapted process that is left-continuous in time at
a.e. `u ∈ (0,T]` (for every `ω`) has its class in the closure of `range eL` (dyadic left-point
approximants `a0 n k = H (k T / 2^n)`, dominated convergence, a.e. ⇒ in measure). -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology EthierKurtz ItoLib
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω}




end StochCalcO3

/-! O6c (8c066573 relay 20): generic Hilbert pieces of O6.  Append after O6b_tail.lean.
`O6_core`: an `L²(μT)` function in the closure of `range eL` orthogonal to every elementary
`efun` vanishes a.e.;  `perp_all`: orthogonality to elementaries with `v < T` suffices;
`proj_fun`: predictable projection `c` of any `F ∈ L²(μT)` (`∫ c ψ = ∫ F ψ` for predictable `ψ`);
`pred_mul`: predictable × bounded adapted a.e.-left-continuous is predictable. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology EthierKurtz ItoLib
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω}

















end StochCalcO3

/-! O6M (8c066573 relay 20): model instance of O6.  Append after O6c_tail.lean in the model dev
file (O6a.lean + O6b_tail + O6c_tail).  With `a' = proj a`, `c = proj (f ∘ snd)` (predictable
projections), every triple stop `τ_N` gives `w_N = a' (Xσ 1[·<τ_N]) + c (Xμ 1[·<τ_N]) ⊥ elementaries`
(O5_gain + proj_fun) and `w_N` predictable (pred_mul), so `w_N = 0` (O6_core); `τ_N = T`
eventually (continuous paths are bounded on `[0,T]`), hence `a' Xσ + c Xμ = 0` μT-a.e. -/

namespace StochCalcO6M

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1b StochCalcO3 StochCalcO3M StochCalcS1R StochCalcHit StochCalcO4M
open StochCalcO5
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]










end StochCalcO6M



/-! O7.1 [U1] energy uniqueness, bounded-coefficient core.  Restriction `resF s` of elementary
combinations to `[0,s)`, its orthogonality to `m s`, and the restricted-norm bound
`‖E[θ | m s]‖ ≤ ‖a 1_{[0,s)}‖` for a stochastic integral `θ` with integrand `a`. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}











end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}





end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}











end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}



end StochCalcO3

/-! O7.1 localization, part L0.  `Rep θ b` : `θ` is the stochastic integral of the predictable
integrand `b` (isometric extension of `TL`).  Basic calculus of `Rep` (distance identity, limits,
existence, uniqueness, orthogonality to `L²(m s)` when `b` vanishes before `s`) and the locality
lemma `L0`: for `A ∈ m t` and `b` vanishing before `t`, `Rep θ b → Rep (1_A θ) (1_A b)`. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}



lemma rep_lim (hW : IncrHyp m W P) (T : ℝ≥0) {x : ℕ → (Elem m T →₀ ℝ)} {θ : Lp ℝ 2 P}
    {b : Lp ℝ 2 (μT P T)} (hx : Tendsto (fun n => TL hW T (x n)) atTop (𝓝 θ))
    (hb : Tendsto (fun n => eL (P := P) hW.le T (x n)) atTop (𝓝 b)) : Rep hW T θ b := by
  refine ⟨mem_closure_of_tendsto hx (Eventually.of_forall fun n => ⟨x n, rfl⟩),
    mem_closure_of_tendsto hb (Eventually.of_forall fun n => ⟨x n, rfl⟩), fun y => ?_⟩
  have h1 : Tendsto (fun n => ⟪TL hW T (x n), TL hW T y⟫_ℝ) atTop (𝓝 ⟪θ, TL hW T y⟫_ℝ) :=
    hx.inner tendsto_const_nhds
  have h2 : Tendsto (fun n => ⟪eL (P := P) hW.le T (x n), eL (P := P) hW.le T y⟫_ℝ) atTop
      (𝓝 ⟪b, eL (P := P) hW.le T y⟫_ℝ) := hb.inner tendsto_const_nhds
  simp only [inner_TL] at h1
  exact tendsto_nhds_unique h1 h2

lemma rep_exists (hW : IncrHyp m W P) (T : ℝ≥0) {b : Lp ℝ 2 (μT P T)}
    (hb : b ∈ closure (Set.range (eL (P := P) hW.le T))) : ∃ θ, Rep hW T θ b := by
  obtain ⟨xs, hxr, hx⟩ := mem_closure_iff_seq_limit.1 hb
  choose y hy using hxr
  have hx' : Tendsto (fun n => eL (P := P) hW.le T (y n)) atTop (𝓝 b) := by
    simp_rw [hy]; exact hx
  have hc : CauchySeq fun n => TL hW T (y n) := by
    have hcu : CauchySeq fun n => eL (P := P) hW.le T (y n) := hx'.cauchySeq
    rw [Metric.cauchySeq_iff] at hcu ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hcu ε hε
    refine ⟨N, fun i hi j hj => ?_⟩
    rw [dist_eq_norm, ← map_sub, norm_TL hW T, map_sub, ← dist_eq_norm]
    exact hN i hi j hj
  obtain ⟨θ, hθ⟩ := cauchySeq_tendsto_of_complete hc
  exact ⟨θ, rep_lim hW T hθ hx'⟩

lemma rep_conv (hW : IncrHyp m W P) (T : ℝ≥0) {θ : Lp ℝ 2 P} {b : Lp ℝ 2 (μT P T)}
    (h : Rep hW T θ b) {x : ℕ → (Elem m T →₀ ℝ)}
    (hb : Tendsto (fun n => eL (P := P) hW.le T (x n)) atTop (𝓝 b)) :
    Tendsto (fun n => TL hW T (x n)) atTop (𝓝 θ) := by
  rw [tendsto_iff_norm_sub_tendsto_zero] at hb ⊢
  simp_rw [rep_dist hW T h]
  exact hb

lemma rep_unique (hW : IncrHyp m W P) (T : ℝ≥0) {θ θ' : Lp ℝ 2 P} {b : Lp ℝ 2 (μT P T)}
    (h : Rep hW T θ b) (h' : Rep hW T θ' b) : θ = θ' := by
  obtain ⟨xs, hxr, hx⟩ := mem_closure_iff_seq_limit.1 h.2.1
  choose y hy using hxr
  have hx' : Tendsto (fun n => eL (P := P) hW.le T (y n)) atTop (𝓝 b) := by
    simp_rw [hy]; exact hx
  exact tendsto_nhds_unique (rep_conv hW T h hx') (rep_conv hW T h' hx')

lemma rep_norm (hW : IncrHyp m W P) (T : ℝ≥0) {θ : Lp ℝ 2 P} {b : Lp ℝ 2 (μT P T)}
    (h : Rep hW T θ b) : ‖θ‖ = ‖b‖ := by
  have := rep_dist hW T h 0
  simpa using this

lemma rep_add (hW : IncrHyp m W P) (T : ℝ≥0) {θ₁ θ₂ : Lp ℝ 2 P} {b₁ b₂ : Lp ℝ 2 (μT P T)}
    (h₁ : Rep hW T θ₁ b₁) (h₂ : Rep hW T θ₂ b₂) : Rep hW T (θ₁ + θ₂) (b₁ + b₂) := by
  obtain ⟨xs, hxr, hx⟩ := mem_closure_iff_seq_limit.1 h₁.2.1
  choose y hy using hxr
  obtain ⟨xs', hxr', hx''⟩ := mem_closure_iff_seq_limit.1 h₂.2.1
  choose y' hy' using hxr'
  have e1 : Tendsto (fun n => eL (P := P) hW.le T (y n)) atTop (𝓝 b₁) := by
    simp_rw [hy]; exact hx
  have e2 : Tendsto (fun n => eL (P := P) hW.le T (y' n)) atTop (𝓝 b₂) := by
    simp_rw [hy']; exact hx''
  refine rep_lim hW T (x := fun n => y n + y' n) ?_ ?_
  · simp_rw [map_add]; exact (rep_conv hW T h₁ e1).add (rep_conv hW T h₂ e2)
  · simp_rw [map_add]; exact e1.add e2

/-- If the integrand vanishes before `s`, the integral is orthogonal to `L²(m s)`. -/
lemma rep_perp (hW : IncrHyp m W P) (T : ℝ≥0) {θ : Lp ℝ 2 P} {b : Lp ℝ 2 (μT P T)}
    (h : Rep hW T θ b) {s : ℝ≥0} (hv : ∀ᵐ z ∂(μT P T), z.1 < (s : ℝ) → b z = 0)
    {g : Ω → ℝ} (hg : Measurable[m s] g) (hg2 : MemLp g 2 P) : ⟪θ, hg2.toLp g⟫_ℝ = 0 := by
  have h0 : (memLp_res (Lp.memLp b) s).toLp _ = 0 := by
    rw [Lp.eq_zero_iff_ae_eq_zero]
    filter_upwards [(memLp_res (Lp.memLp b) s).coeFn_toLp, hv] with z h1 h2
    rw [h1]
    by_cases hz : z.1 < (s : ℝ)
    · simp [h2 hz]
    · simp [ind, Set.indicator_apply, hz]
  have h1 := S1 hW T h.1 h.2.2 h.2.1 s hg hg2
  have h2 := S1 hW T h.1 h.2.2 h.2.1 s (g := -g) (hg.neg : Measurable[m s] (-g)) hg2.neg
  rw [h0, norm_zero, zero_mul] at h1 h2
  rw [MemLp.toLp_neg hg2, inner_neg_right] at h2
  linarith

/-- The indicator of `A` as a real function. -/
noncomputable def oneA (A : Set Ω) (ω : Ω) : ℝ := A.indicator (fun _ => (1 : ℝ)) ω

lemma abs_oneA_le (A : Set Ω) (ω : Ω) : |oneA A ω| ≤ 1 := by
  classical
  unfold oneA; rw [Set.indicator_apply]; split_ifs <;> simp

lemma oneA_univ (ω : Ω) : oneA (Set.univ : Set Ω) ω = 1 := by simp [oneA]

lemma oneA_meas {t : ℝ≥0} {A : Set Ω} (hA : MeasurableSet[m t] A) : Measurable[m t] (oneA A) := by
  unfold oneA; exact measurable_const.indicator hA

lemma univ_meas (t : ℝ≥0) : MeasurableSet[m t] (Set.univ : Set Ω) := @MeasurableSet.univ Ω (m t)

lemma ind_max (u v t : ℝ≥0) (r : ℝ) :
    ind (max u t) (max v t) r = ind u v r * (1 - ind 0 t r) := by
  have hu : (0 : ℝ) ≤ u := u.2
  simp only [ind, Set.indicator_apply, Set.mem_Ico, NNReal.coe_max, NNReal.coe_zero, max_le_iff,
    lt_max_iff]
  by_cases h1 : (u : ℝ) ≤ r
  · by_cases h3 : (t : ℝ) ≤ r
    · have h3' : ¬ r < (t : ℝ) := not_lt.2 h3
      by_cases h2 : r < (v : ℝ)
      · simp [h1, h2, h3, h3']
      · simp [h1, h2, h3, h3']
    · have h3' : r < (t : ℝ) := lt_of_not_ge h3
      have h0 : (0 : ℝ) ≤ r := hu.trans h1
      by_cases h2 : r < (v : ℝ)
      · simp [h1, h2, h3, h3', h0]
      · simp [h1, h2, h3]
  · simp [h1]

lemma abs_one_sub_ind_le (t : ℝ≥0) (r : ℝ) : |1 - ind 0 t r| ≤ 1 := by
  unfold ind; rw [Set.indicator_apply]; split_ifs <;> simp

/-- Tail-and-indicator modification of an elementary process: `1_A Y 1_[max u t, max v t)`. -/
noncomputable def tailI (hmono : Monotone m) {T t : ℝ≥0} (htT : t ≤ T) {A : Set Ω}
    (hA : MeasurableSet[m t] A) (i : Elem m T) : Elem m T where
  u := max i.u t
  v := max i.v t
  huv := max_le_max i.huv le_rfl
  hvT := max_le i.hvT htT
  Y := fun ω => oneA A ω * i.Y ω
  hY := ((oneA_meas hA).mono (hmono (le_max_right _ _)) le_rfl).mul
    (i.hY.mono (hmono (le_max_left _ _)) le_rfl)
  C := i.C
  hC := fun ω => by
    rw [abs_mul]
    calc |oneA A ω| * |i.Y ω| ≤ 1 * |i.Y ω| :=
          mul_le_mul_of_nonneg_right (abs_oneA_le A ω) (abs_nonneg _)
      _ ≤ i.C := by rw [one_mul]; exact i.hC ω

lemma efun_tailI (hmono : Monotone m) {T t : ℝ≥0} (htT : t ≤ T) {A : Set Ω}
    (hA : MeasurableSet[m t] A) (i : Elem m T) (z : ℝ × Ω) :
    efun (tailI hmono htT hA i) z = oneA A z.2 * (efun i z * (1 - ind 0 t z.1)) := by
  show ind (max i.u t) (max i.v t) z.1 * (oneA A z.2 * i.Y z.2) = _
  rw [ind_max]
  simp only [efun]
  ring

lemma ifun_tailI (hmono : Monotone m) {T t : ℝ≥0} (htT : t ≤ T) {A : Set Ω}
    (hA : MeasurableSet[m t] A) (i : Elem m T) (ω : Ω) :
    ifun W (tailI hmono htT hA i) ω = oneA A ω * ifun W (tailI hmono htT (univ_meas t) i) ω := by
  show oneA A ω * i.Y ω * (W (max i.v t) ω - W (max i.u t) ω) =
    oneA A ω * (oneA Set.univ ω * i.Y ω * (W (max i.v t) ω - W (max i.u t) ω))
  rw [oneA_univ]; ring

noncomputable def tailF (hmono : Monotone m) {T t : ℝ≥0} (htT : t ≤ T) {A : Set Ω}
    (hA : MeasurableSet[m t] A) (x : Elem m T →₀ ℝ) : Elem m T →₀ ℝ :=
  Finsupp.mapDomain (tailI hmono htT hA) x

lemma comb_tailF (hmono : Monotone m) {T t : ℝ≥0} (htT : t ≤ T) {A : Set Ω}
    (hA : MeasurableSet[m t] A) (x : Elem m T →₀ ℝ) (z : ℝ × Ω) :
    (tailF hmono htT hA x).sum (fun i c => c * efun i z) =
      oneA A z.2 * (x.sum (fun i c => c * efun i z) * (1 - ind 0 t z.1)) := by
  unfold tailF
  rw [Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
  simp only [efun_tailI, Finsupp.sum, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma icomb_tailF (hmono : Monotone m) {T t : ℝ≥0} (htT : t ≤ T) {A : Set Ω}
    (hA : MeasurableSet[m t] A) (x : Elem m T →₀ ℝ) (ω : Ω) :
    (tailF hmono htT hA x).sum (fun i c => c * ifun W i ω) =
      oneA A ω * (tailF hmono htT (univ_meas t) x).sum (fun i c => c * ifun W i ω) := by
  unfold tailF
  rw [Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _),
    Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
  simp only [ifun_tailI hmono htT hA, Finsupp.sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma tail_eL_le (hW : IncrHyp m W P) {T t : ℝ≥0} (htT : t ≤ T) {A : Set Ω}
    (hA : MeasurableSet[m t] A) {b b' : Lp ℝ 2 (μT P T)}
    (hv : ∀ᵐ z ∂(μT P T), z.1 < (t : ℝ) → b z = 0)
    (hb' : b' =ᵐ[μT P T] fun z => oneA A z.2 * b z) (x : Elem m T →₀ ℝ) :
    ‖eL (P := P) hW.le T (tailF hW.mono htT hA x) - b'‖ ≤ ‖eL (P := P) hW.le T x - b‖ := by
  refine Lp.norm_le_norm_of_ae_le ?_
  filter_upwards [Lp.coeFn_sub (eL (P := P) hW.le T (tailF hW.mono htT hA x)) b',
    Lp.coeFn_sub (eL (P := P) hW.le T x) b, coe_eL (P := P) hW.le T (tailF hW.mono htT hA x),
    coe_eL (P := P) hW.le T x, hb', hv] with z h1 h2 h3 h4 h5 h6
  rw [h1, h2, Pi.sub_apply, Pi.sub_apply, h3, h4, h5, comb_tailF]
  have hbz : b z - b z * (1 - ind 0 t z.1) = 0 := by
    by_cases hz : z.1 < (t : ℝ)
    · rw [h6 hz]; ring
    · have : ind 0 t z.1 = 0 := by simp [ind, Set.indicator_apply, hz]
      rw [this]; ring
  have key : oneA A z.2 * (x.sum (fun i c => c * efun i z) * (1 - ind 0 t z.1)) -
      oneA A z.2 * b z =
      (oneA A z.2 * (1 - ind 0 t z.1)) * (x.sum (fun i c => c * efun i z) - b z) := by
    linear_combination (-(oneA A z.2)) * hbz
  rw [key, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
  refine mul_le_of_le_one_left (abs_nonneg _) ?_
  rw [abs_mul]
  exact mul_le_one₀ (abs_oneA_le A z.2) (abs_nonneg _) (abs_one_sub_ind_le t z.1)

lemma tail_TL_le (hW : IncrHyp m W P) {T t : ℝ≥0} (htT : t ≤ T) {A : Set Ω}
    (hA : MeasurableSet[m t] A) {θ θ' : Lp ℝ 2 P}
    (hθ' : θ' =ᵐ[P] fun ω => oneA A ω * θ ω) (x : Elem m T →₀ ℝ) :
    ‖TL hW T (tailF hW.mono htT hA x) - θ'‖ ≤
      ‖TL hW T (tailF hW.mono htT (univ_meas t) x) - θ‖ := by
  refine Lp.norm_le_norm_of_ae_le ?_
  filter_upwards [Lp.coeFn_sub (TL hW T (tailF hW.mono htT hA x)) θ',
    Lp.coeFn_sub (TL hW T (tailF hW.mono htT (univ_meas t) x)) θ,
    coe_TL hW T (tailF hW.mono htT hA x), coe_TL hW T (tailF hW.mono htT (univ_meas t) x), hθ']
    with ω h1 h2 h3 h4 h5
  rw [h1, h2, Pi.sub_apply, Pi.sub_apply, h3, h4, h5, icomb_tailF, ← mul_sub, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_mul]
  exact mul_le_of_le_one_left (abs_nonneg _) (abs_oneA_le A ω)

/-- L0 locality: for `A ∈ m t` and an integrand vanishing before `t`, `I(1_A b) = 1_A I(b)`. -/
theorem L0 (hW : IncrHyp m W P) (T : ℝ≥0) {t : ℝ≥0} (htT : t ≤ T) {A : Set Ω}
    (hA : MeasurableSet[m t] A) {θ : Lp ℝ 2 P} {b : Lp ℝ 2 (μT P T)} (h : Rep hW T θ b)
    (hv : ∀ᵐ z ∂(μT P T), z.1 < (t : ℝ) → b z = 0)
    {θ' : Lp ℝ 2 P} (hθ' : θ' =ᵐ[P] fun ω => oneA A ω * θ ω)
    {b' : Lp ℝ 2 (μT P T)} (hb' : b' =ᵐ[μT P T] fun z => oneA A z.2 * b z) :
    Rep hW T θ' b' := by
  obtain ⟨xs, hxr, hx⟩ := mem_closure_iff_seq_limit.1 h.1
  choose y hy using hxr
  have hx' : Tendsto (fun n => TL hW T (y n)) atTop (𝓝 θ) := by simp_rw [hy]; exact hx
  have hE := eL_tendsto hW T h.2.2 h.2.1 hx'
  have hEn : Tendsto (fun n => ‖eL (P := P) hW.le T (y n) - b‖) atTop (𝓝 0) :=
    (tendsto_iff_norm_sub_tendsto_zero).1 hE
  have hU : Tendsto (fun n => eL (P := P) hW.le T (tailF hW.mono htT (univ_meas t) (y n)))
      atTop (𝓝 b) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _)
      (fun n => tail_eL_le hW htT (univ_meas t) hv ?_ (y n)) hEn
    exact Eventually.of_forall fun z => by simp [oneA_univ]
  have hUT := rep_conv hW T h hU
  have hA1 : Tendsto (fun n => eL (P := P) hW.le T (tailF hW.mono htT hA (y n))) atTop
      (𝓝 b') := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => tail_eL_le hW htT hA hv hb' (y n)) hEn
  have hA2 : Tendsto (fun n => TL hW T (tailF hW.mono htT hA (y n))) atTop (𝓝 θ') := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => tail_TL_le hW htT hA hθ' (y n))
      ((tendsto_iff_norm_sub_tendsto_zero).1 hUT)
  exact rep_lim hW T hA2 hA1

end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}

/-! L1: grid stopping times.  For `τ` with finitely many values `t ∈ S` (`{τ = t} ∈ m t`) and
`δ = I(1_{τ ≤ r} a)`, `δ ⊥ ξ 1_{u < τ}` for bounded `m u`-measurable `ξ`. -/

lemma coeFn_fsum {α : Type*} [MeasurableSpace α] {μ : Measure α} {ι : Type*} (S : Finset ι)
    (f : ι → Lp ℝ 2 μ) : ⇑(∑ i ∈ S, f i) =ᵐ[μ] fun x => ∑ i ∈ S, f i x := by
  classical
  refine Finset.induction_on S ?_ ?_
  · simp only [Finset.sum_empty]; exact Lp.coeFn_zero ..
  · intro j S hj ih
    rw [Finset.sum_insert hj]
    filter_upwards [Lp.coeFn_add (f j) (∑ i ∈ S, f i), ih] with x h1 h2
    rw [h1, Pi.add_apply, h2, Finset.sum_insert hj]

lemma rep_zero (hW : IncrHyp m W P) (T : ℝ≥0) : Rep hW T (0 : Lp ℝ 2 P) (0 : Lp ℝ 2 (μT P T)) :=
  rep_lim hW T (x := fun _ => 0) (by simp only [map_zero]; exact tendsto_const_nhds)
    (by simp only [map_zero]; exact tendsto_const_nhds)

lemma rep_sum (hW : IncrHyp m W P) (T : ℝ≥0) {ι : Type*} (S : Finset ι) {θ : ι → Lp ℝ 2 P}
    {b : ι → Lp ℝ 2 (μT P T)} (h : ∀ i ∈ S, Rep hW T (θ i) (b i)) :
    Rep hW T (∑ i ∈ S, θ i) (∑ i ∈ S, b i) := by
  classical
  revert h
  refine Finset.induction_on S ?_ ?_
  · intro _; simpa using rep_zero hW T
  · intro j S hj ih h
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    exact rep_add hW T (h j (Finset.mem_insert_self j S))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma memLp_oneA_mul {A : Set Ω} (hA : MeasurableSet A) (f : Lp ℝ 2 P) :
    MemLp (fun ω => oneA A ω * f ω) 2 P := by
  have hm : Measurable (oneA A) := by unfold oneA; exact measurable_const.indicator hA
  refine (Lp.memLp f).of_le (hm.aestronglyMeasurable.mul (Lp.memLp f).aestronglyMeasurable)
    (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
  exact mul_le_of_le_one_left (abs_nonneg _) (abs_oneA_le A ω)

lemma memLp_oneA_mulT {T : ℝ≥0} {A : Set Ω} (hA : MeasurableSet A) (f : Lp ℝ 2 (μT P T)) :
    MemLp (fun z : ℝ × Ω => oneA A z.2 * f z) 2 (μT P T) := by
  have hm : Measurable (oneA A) := by unfold oneA; exact measurable_const.indicator hA
  refine (Lp.memLp f).of_le ((hm.comp measurable_snd).aestronglyMeasurable.mul
    (Lp.memLp f).aestronglyMeasurable) (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
  exact mul_le_of_le_one_left (abs_nonneg _) (abs_oneA_le A z.2)

lemma memLp_tl {T : ℝ≥0} {a : ℝ × Ω → ℝ} (ha : MemLp a 2 (μT P T)) (t : ℝ≥0) :
    MemLp (fun z => a z * (1 - ind 0 t z.1)) 2 (μT P T) := by
  have hm : Measurable fun z : ℝ × Ω => 1 - ind 0 t z.1 :=
    measurable_const.sub ((ind_meas 0 t).comp measurable_fst)
  refine ha.of_le (ha.aestronglyMeasurable.mul hm.aestronglyMeasurable)
    (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (abs_one_sub_ind_le _ _)

lemma res_mem (hW : IncrHyp m W P) (T : ℝ≥0) {a : Lp ℝ 2 (μT P T)}
    (haP : a ∈ closure (Set.range (eL (P := P) hW.le T))) (s : ℝ≥0) :
    (memLp_res (Lp.memLp a) s).toLp _ ∈ closure (Set.range (eL (P := P) hW.le T)) := by
  obtain ⟨xs, hxr, hx⟩ := mem_closure_iff_seq_limit.1 haP
  choose y hy using hxr
  have hx' : Tendsto (fun n => eL (P := P) hW.le T (y n)) atTop (𝓝 a) := by
    simp_rw [hy]; exact hx
  have hres : Tendsto (fun n => eL (P := P) hW.le T (resF s (y n))) atTop
      (𝓝 ((memLp_res (Lp.memLp a) s).toLp _)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => norm_res_sub_le hW.le a s (y n))
      ((tendsto_iff_norm_sub_tendsto_zero).1 hx')
  exact mem_closure_of_tendsto hres (Eventually.of_forall fun n => ⟨_, rfl⟩)

lemma tl_mem (hW : IncrHyp m W P) (T : ℝ≥0) {a : Lp ℝ 2 (μT P T)}
    (haP : a ∈ closure (Set.range (eL (P := P) hW.le T))) (t : ℝ≥0) :
    (memLp_tl (Lp.memLp a) t).toLp _ ∈ closure (Set.range (eL (P := P) hW.le T)) := by
  have e : (memLp_tl (Lp.memLp a) t).toLp _ = a - (memLp_res (Lp.memLp a) t).toLp _ := by
    refine Lp.ext ?_
    filter_upwards [(memLp_tl (Lp.memLp a) t).coeFn_toLp,
      Lp.coeFn_sub a ((memLp_res (Lp.memLp a) t).toLp _),
      (memLp_res (Lp.memLp a) t).coeFn_toLp] with z h1 h2 h3
    simp only [h1, h2, Pi.sub_apply, h3]
    ring
  rw [e]
  exact (mem_Pred_iff hW.le T _).1 ((Pred (P := P) hW.le T).sub_mem
    ((mem_Pred_iff hW.le T a).2 haP) ((mem_Pred_iff hW.le T _).2 (res_mem hW T haP t)))

lemma rep_perp_int (hW : IncrHyp m W P) (T : ℝ≥0) {θ : Lp ℝ 2 P} {b : Lp ℝ 2 (μT P T)}
    (h : Rep hW T θ b) {s : ℝ≥0} (hv : ∀ᵐ z ∂(μT P T), z.1 < (s : ℝ) → b z = 0)
    {g : Ω → ℝ} (hg : Measurable[m s] g) {C : ℝ} (hC : ∀ ω, |g ω| ≤ C) :
    ∫ ω, θ ω * g ω ∂P = 0 := by
  have hg2 : MemLp g 2 P := MemLp.of_bound (hg.mono (hW.le s) le_rfl).aestronglyMeasurable C
    (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hC ω)
  have h0 := rep_perp hW T h hv hg hg2
  rw [L2.inner_def] at h0
  rw [← h0]
  refine integral_congr_ae ?_
  filter_upwards [hg2.coeFn_toLp] with ω h1
  rw [h1, RCLike.inner_apply', conj_trivial]

lemma tl_vanish {T : ℝ≥0} (a : Lp ℝ 2 (μT P T)) (t : ℝ≥0) :
    ∀ᵐ z ∂(μT P T), z.1 < (t : ℝ) → ((memLp_tl (Lp.memLp a) t).toLp _ : ℝ × Ω → ℝ) z = 0 := by
  filter_upwards [(memLp_tl (Lp.memLp a) t).coeFn_toLp, ae_fst_Ico (P := P) T] with z h1 h2 hz
  rw [h1]
  have : ind 0 t z.1 = 1 := by simp [ind, Set.indicator_apply, h2.1, hz]
  simp [this]

theorem L1 (hW : IncrHyp m W P) (T : ℝ≥0) {θ : Lp ℝ 2 P} {a : Lp ℝ 2 (μT P T)}
    (h : Rep hW T θ a) {τ : Ω → ℝ≥0} (S : Finset ℝ≥0) (hS : ∀ ω, τ ω ∈ S)
    (hST : ∀ t ∈ S, t ≤ T) (hτ : ∀ t ∈ S, MeasurableSet[m t] {ω | τ ω = t})
    {δ : Lp ℝ 2 P} {bc : Lp ℝ 2 (μT P T)}
    (hbc : bc =ᵐ[μT P T] fun z => (if (τ z.2 : ℝ) ≤ z.1 then (1 : ℝ) else 0) * a z)
    (hδ : Rep hW T δ bc) (u : ℝ≥0) {ξ : Ω → ℝ} (hξ : Measurable[m u] ξ) {C : ℝ}
    (hC : ∀ ω, |ξ ω| ≤ C) :
    ∫ ω, δ ω * (ξ ω * (if u < τ ω then (1 : ℝ) else 0)) ∂P = 0 := by
  classical
  have hex : ∀ t : ℝ≥0, ∃ d : Lp ℝ 2 P, Rep hW T d ((memLp_tl (Lp.memLp a) t).toLp _) :=
    fun t => rep_exists hW T (tl_mem hW T h.2.1 t)
  choose d hd using hex
  have hτ' : ∀ t, MeasurableSet[m t] {ω | τ ω = t} := by
    intro t
    by_cases ht : t ∈ S
    · exact hτ t ht
    · have e : {ω | τ ω = t} = ∅ := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        intro e; exact ht (e ▸ hS ω)
      rw [e]; exact @MeasurableSet.empty Ω (m t)
  have hA0 : ∀ t, MeasurableSet {ω | τ ω = t} := fun t => hW.le t _ (hτ' t)
  have hrep : ∀ t ∈ S, Rep hW T ((memLp_oneA_mul (hA0 t) (d t)).toLp _)
      ((memLp_oneA_mulT (hA0 t) ((memLp_tl (Lp.memLp a) t).toLp _)).toLp _) := fun t ht =>
    L0 hW T (hST t ht) (hτ' t) (hd t) (tl_vanish a t) (memLp_oneA_mul (hA0 t) (d t)).coeFn_toLp
      (memLp_oneA_mulT (hA0 t) _).coeFn_toLp
  have hsum := rep_sum hW T S (θ := fun t => (memLp_oneA_mul (hA0 t) (d t)).toLp _)
    (b := fun t => (memLp_oneA_mulT (hA0 t) ((memLp_tl (Lp.memLp a) t).toLp _)).toLp _) hrep
  have hbeq : (∑ t ∈ S, (memLp_oneA_mulT (hA0 t) ((memLp_tl (Lp.memLp a) t).toLp _)).toLp _) =
      bc := by
    refine Lp.ext ?_
    filter_upwards [coeFn_fsum S
        (fun t => (memLp_oneA_mulT (hA0 t) ((memLp_tl (Lp.memLp a) t).toLp _)).toLp _),
      hbc, ae_fst_Ico (P := P) T,
      (Filter.eventually_all_finset S).2 fun t _ =>
        (memLp_oneA_mulT (hA0 t) ((memLp_tl (Lp.memLp a) t).toLp _)).coeFn_toLp,
      (Filter.eventually_all_finset S).2 fun t _ => (memLp_tl (Lp.memLp a) t).coeFn_toLp]
      with z h1 h2 h3 h4 h5
    have e : ∀ t ∈ S, ((memLp_oneA_mulT (hA0 t) ((memLp_tl (Lp.memLp a) t).toLp _)).toLp _ :
        ℝ × Ω → ℝ) z = oneA {ω | τ ω = t} z.2 * (a z * (1 - ind 0 t z.1)) := fun t ht => by
      rw [h4 t ht, h5 t ht]
    rw [h1, h2, Finset.sum_congr rfl e, Finset.sum_eq_single (τ z.2)]
    · simp only [oneA, Set.indicator_apply, Set.mem_setOf_eq, if_true, one_mul]
      by_cases hle : (τ z.2 : ℝ) ≤ z.1
      · have : ind 0 (τ z.2) z.1 = 0 := by simp [ind, Set.indicator_apply, not_lt.2 hle]
        simp [hle, this]
      · have : ind 0 (τ z.2) z.1 = 1 := by
          simp [ind, Set.indicator_apply, h3.1, lt_of_not_ge hle]
        simp [hle, this]
    · intro t _ ht
      simp only [oneA, Set.indicator_apply, Set.mem_setOf_eq]
      rw [if_neg (Ne.symm ht)]; ring
    · intro hn; exact absurd (hS z.2) hn
  have hδeq : δ = ∑ t ∈ S, (memLp_oneA_mul (hA0 t) (d t)).toLp _ :=
    rep_unique hW T hδ (by rw [← hbeq]; exact hsum)
  have hlt : MeasurableSet {ω | u < τ ω} := by
    have e : {ω | u < τ ω} = ⋃ t ∈ S.filter (fun t => u < t), {ω | τ ω = t} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_filter, exists_prop]
      constructor
      · intro h'; exact ⟨τ ω, ⟨hS ω, h'⟩, rfl⟩
      · rintro ⟨t, ⟨_, ht⟩, e⟩; rw [e]; exact ht
    rw [e]; exact Finset.measurableSet_biUnion _ fun t _ => hA0 t
  have hζm : Measurable fun ω => ξ ω * (if u < τ ω then (1 : ℝ) else 0) :=
    (hξ.mono (hW.le u) le_rfl).mul (Measurable.ite hlt measurable_const measurable_const)
  have hζ2 : MemLp (fun ω => ξ ω * (if u < τ ω then (1 : ℝ) else 0)) 2 P :=
    MemLp.of_bound hζm.aestronglyMeasurable C (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_mul]
      refine (mul_le_of_le_one_right (abs_nonneg _) ?_).trans (hC ω)
      split_ifs <;> simp)
  rw [hδeq]
  calc ∫ ω, (∑ t ∈ S, (memLp_oneA_mul (hA0 t) (d t)).toLp _ : Lp ℝ 2 P) ω *
        (ξ ω * (if u < τ ω then (1 : ℝ) else 0)) ∂P
      = ∫ ω, ∑ t ∈ S, ((memLp_oneA_mul (hA0 t) (d t)).toLp _ : Ω → ℝ) ω *
        (ξ ω * (if u < τ ω then (1 : ℝ) else 0)) ∂P := by
        refine integral_congr_ae ?_
        filter_upwards [coeFn_fsum S (fun t => (memLp_oneA_mul (hA0 t) (d t)).toLp _)] with ω h'
        rw [h', Finset.sum_mul]
    _ = ∑ t ∈ S, ∫ ω, ((memLp_oneA_mul (hA0 t) (d t)).toLp _ : Ω → ℝ) ω *
        (ξ ω * (if u < τ ω then (1 : ℝ) else 0)) ∂P :=
        integral_finset_sum S fun t _ => (Lp.memLp _).integrable_mul hζ2
    _ = 0 := by
      refine Finset.sum_eq_zero fun t _ => ?_
      have e1 : ∫ ω, ((memLp_oneA_mul (hA0 t) (d t)).toLp _ : Ω → ℝ) ω *
          (ξ ω * (if u < τ ω then (1 : ℝ) else 0)) ∂P =
          ∫ ω, d t ω * (if u < t then oneA {ω | τ ω = t} ω * ξ ω else 0) ∂P := by
        refine integral_congr_ae ?_
        filter_upwards [(memLp_oneA_mul (hA0 t) (d t)).coeFn_toLp] with ω h'
        rw [h']
        by_cases hω : τ ω = t
        · by_cases hut : u < t
          · simp [oneA, Set.indicator_apply, hω, hut]
          · simp [oneA, Set.indicator_apply, hω, hut]
        · simp [oneA, Set.indicator_apply, hω]
      rw [e1]
      by_cases hut : u < t
      · simp only [if_pos hut]
        refine rep_perp_int hW T (hd t) (tl_vanish a t) (g := fun ω => oneA {ω | τ ω = t} ω * ξ ω)
          ((oneA_meas (hτ' t)).mul (hξ.mono (hW.mono hut.le) le_rfl)) (C := C) fun ω => ?_
        rw [abs_mul]
        exact (mul_le_of_le_one_left (abs_nonneg _) (abs_oneA_le _ ω)).trans (hC ω)
      · simp only [if_neg hut, mul_zero, integral_zero]

end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}

/-! L2: general stopping times `τ ≤ T`, by the dyadic ceilings `gc T n τ ↓ τ`. -/

lemma rep_neg (hW : IncrHyp m W P) (T : ℝ≥0) {θ : Lp ℝ 2 P} {b : Lp ℝ 2 (μT P T)}
    (h : Rep hW T θ b) : Rep hW T (-θ) (-b) := by
  obtain ⟨xs, hxr, hx⟩ := mem_closure_iff_seq_limit.1 h.2.1
  choose y hy using hxr
  have e1 : Tendsto (fun n => eL (P := P) hW.le T (y n)) atTop (𝓝 b) := by
    simp_rw [hy]; exact hx
  refine rep_lim hW T (x := fun n => -y n) ?_ ?_
  · simp_rw [map_neg]; exact (rep_conv hW T h e1).neg
  · simp_rw [map_neg]; exact e1.neg

lemma rep_sub (hW : IncrHyp m W P) (T : ℝ≥0) {θ₁ θ₂ : Lp ℝ 2 P} {b₁ b₂ : Lp ℝ 2 (μT P T)}
    (h₁ : Rep hW T θ₁ b₁) (h₂ : Rep hW T θ₂ b₂) : Rep hW T (θ₁ - θ₂) (b₁ - b₂) := by
  simpa [sub_eq_add_neg] using rep_add hW T h₁ (rep_neg hW T h₂)

lemma int_eq_inner (f : Lp ℝ 2 P) {g : Ω → ℝ} (hg2 : MemLp g 2 P) :
    ∫ ω, f ω * g ω ∂P = ⟪f, hg2.toLp g⟫_ℝ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hg2.coeFn_toLp] with ω h1
  rw [h1, RCLike.inner_apply', conj_trivial]

lemma eq_meas_of_stop (hmono : Monotone m) {τ : Ω → ℝ≥0} (S : Finset ℝ≥0) (hS : ∀ ω, τ ω ∈ S)
    (hτ : ∀ s, MeasurableSet[m s] {ω | τ ω ≤ s}) (t : ℝ≥0) :
    MeasurableSet[m t] {ω | τ ω = t} := by
  classical
  have e : {ω | τ ω = t} = {ω | τ ω ≤ t} \ ⋃ s ∈ S.filter (fun s => s < t), {ω | τ ω ≤ s} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_diff, Set.mem_iUnion, Finset.mem_filter, exists_prop]
    constructor
    · intro e
      refine ⟨e.le, ?_⟩
      rintro ⟨s, ⟨_, hs⟩, h⟩
      exact absurd (lt_of_le_of_lt h hs) (by rw [e]; exact lt_irrefl _)
    · rintro ⟨h1, h2⟩
      by_contra hne
      exact h2 ⟨τ ω, ⟨hS ω, lt_of_le_of_ne h1 hne⟩, le_rfl⟩
  rw [e]
  exact (hτ t).diff (Finset.measurableSet_biUnion _ fun s hs =>
    hmono (Finset.mem_filter.1 hs).2.le _ (hτ s))

lemma ae_ne_graph (T : ℝ≥0) {τ : Ω → ℝ≥0} (hτm : Measurable τ) :
    ∀ᵐ z ∂(μT P T), z.1 ≠ (τ z.2 : ℝ) := by
  have hp : MeasurableSet {z : ℝ × Ω | z.1 ≠ (τ z.2 : ℝ)} :=
    (measurableSet_eq_fun measurable_fst (hτm.comp measurable_snd).coe_nnreal_real).compl
  have h2 : ∀ᵐ z ∂(P.prod (volume.restrict (Set.Ico (0 : ℝ) T))),
      z.swap.1 ≠ (τ z.swap.2 : ℝ) := by
    refine (Measure.ae_prod_iff_ae_ae (measurable_swap hp)).2 (Eventually.of_forall fun ω => ?_)
    refine ae_restrict_of_ae ?_
    have : ∀ᵐ r ∂(volume : Measure ℝ), r ≠ (τ ω : ℝ) := by
      rw [ae_iff]; simp
    exact this
  unfold μT
  rw [← Measure.prod_swap, ae_map_iff measurable_swap.aemeasurable hp]
  exact h2

/-- Dyadic ceiling capped at `T`. -/
noncomputable def gc (T : ℝ≥0) (n : ℕ) (x : ℝ≥0) : ℝ≥0 :=
  min T ((⌈(x : ℝ) * 2 ^ n⌉₊ : ℝ≥0) / 2 ^ n)

/-- Its (finite) value set. -/
noncomputable def gcS (T : ℝ≥0) (n : ℕ) : Finset ℝ≥0 :=
  (Finset.range (⌈(T : ℝ) * 2 ^ n⌉₊ + 1)).image (fun k : ℕ => min T ((k : ℝ≥0) / 2 ^ n))

lemma gc_real (T : ℝ≥0) (n : ℕ) (x : ℝ≥0) :
    (gc T n x : ℝ) = min (T : ℝ) ((⌈(x : ℝ) * 2 ^ n⌉₊ : ℝ) / 2 ^ n) := by
  simp [gc]

lemma le_gc {T x : ℝ≥0} (n : ℕ) (hx : x ≤ T) : x ≤ gc T n x := by
  rw [← NNReal.coe_le_coe, gc_real]
  refine le_min (by exact_mod_cast hx) ?_
  rw [le_div_iff₀ (by positivity)]
  exact Nat.le_ceil _

lemma gc_le_add (T : ℝ≥0) (n : ℕ) (x : ℝ≥0) : (gc T n x : ℝ) ≤ x + 1 / 2 ^ n := by
  rw [gc_real]
  refine (min_le_right _ _).trans ?_
  rw [div_le_iff₀ (by positivity), add_mul, one_div, inv_mul_cancel₀ (by positivity)]
  exact (Nat.ceil_lt_add_one (by positivity)).le

lemma gc_le (T : ℝ≥0) (n : ℕ) (x : ℝ≥0) : gc T n x ≤ T := min_le_left _ _

lemma gc_tendsto {T x : ℝ≥0} (hx : x ≤ T) :
    Tendsto (fun n => (gc T n x : ℝ)) atTop (𝓝 (x : ℝ)) := by
  have h0 : Tendsto (fun n : ℕ => (1 : ℝ) / 2 ^ n) atTop (𝓝 0) := by
    simp_rw [← one_div_pow]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h1 : Tendsto (fun n : ℕ => (x : ℝ) + 1 / 2 ^ n) atTop (𝓝 (x : ℝ)) := by
    simpa using (tendsto_const_nhds (x := (x : ℝ))).add h0
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1
    (fun n => by exact_mod_cast le_gc n hx) (fun n => gc_le_add T n x)

lemma gc_mem {T x : ℝ≥0} (n : ℕ) (hx : x ≤ T) : gc T n x ∈ gcS T n := by
  refine Finset.mem_image.2 ⟨⌈(x : ℝ) * 2 ^ n⌉₊, Finset.mem_range.2 (Nat.lt_succ_of_le
    (Nat.ceil_mono ?_)), rfl⟩
  have : (x : ℝ) ≤ T := by exact_mod_cast hx
  gcongr

lemma gcS_le {T t : ℝ≥0} {n : ℕ} (ht : t ∈ gcS T n) : t ≤ T := by
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.1 ht
  exact min_le_left _ _

lemma gc_stop (hmono : Monotone m) {T : ℝ≥0} {τ : Ω → ℝ≥0} (hτ : ∀ s, MeasurableSet[m s] {ω | τ ω ≤ s})
    (n : ℕ) (s : ℝ≥0) : MeasurableSet[m s] {ω | gc T n (τ ω) ≤ s} := by
  by_cases hs : T ≤ s
  · have e : {ω | gc T n (τ ω) ≤ s} = Set.univ :=
      Set.eq_univ_of_forall fun ω => (gc_le T n (τ ω)).trans hs
    rw [e]; exact @MeasurableSet.univ Ω (m s)
  · have hsT : (s : ℝ) < T := by exact_mod_cast lt_of_not_ge hs
    have h2 : (0 : ℝ) < 2 ^ n := by positivity
    have hs0 : (0 : ℝ) ≤ (s : ℝ) * 2 ^ n := by positivity
    obtain ⟨s', hs'⟩ : ∃ s' : ℝ≥0, (s' : ℝ) = (⌊(s : ℝ) * 2 ^ n⌋₊ : ℝ) / 2 ^ n :=
      ⟨⟨(⌊(s : ℝ) * 2 ^ n⌋₊ : ℝ) / 2 ^ n, by positivity⟩, rfl⟩
    have hss : s' ≤ s := by
      rw [← NNReal.coe_le_coe, hs', div_le_iff₀ h2]
      exact Nat.floor_le hs0
    have e : {ω | gc T n (τ ω) ≤ s} = {ω | τ ω ≤ s'} := by
      ext ω
      simp only [Set.mem_setOf_eq]
      rw [← NNReal.coe_le_coe, ← NNReal.coe_le_coe, gc_real, hs', min_le_iff,
        or_iff_right (not_le.2 hsT), div_le_iff₀ h2, le_div_iff₀ h2]
      constructor
      · intro h
        have := Nat.le_floor h
        exact (Nat.le_ceil _).trans (by exact_mod_cast this)
      · intro h
        have := Nat.ceil_le.2 h
        exact (by exact_mod_cast this : (⌈(τ ω : ℝ) * 2 ^ n⌉₊ : ℝ) ≤ ⌊(s : ℝ) * 2 ^ n⌋₊).trans
          (Nat.floor_le hs0)
    rw [e]
    exact hmono hss _ (hτ s')

theorem L1ex (hW : IncrHyp m W P) (T : ℝ≥0) {a : Lp ℝ 2 (μT P T)}
    (haP : a ∈ closure (Set.range (eL (P := P) hW.le T))) {τ : Ω → ℝ≥0} (S : Finset ℝ≥0) (hS : ∀ ω, τ ω ∈ S)
    (hST : ∀ t ∈ S, t ≤ T) (hτ : ∀ t ∈ S, MeasurableSet[m t] {ω | τ ω = t})
    {bc : Lp ℝ 2 (μT P T)}
    (hbc : bc =ᵐ[μT P T] fun z => (if (τ z.2 : ℝ) ≤ z.1 then (1 : ℝ) else 0) * a z)
 :
    ∃ δ, Rep hW T δ bc := by
  classical
  have hex : ∀ t : ℝ≥0, ∃ d : Lp ℝ 2 P, Rep hW T d ((memLp_tl (Lp.memLp a) t).toLp _) :=
    fun t => rep_exists hW T (tl_mem hW T haP t)
  choose d hd using hex
  have hτ' : ∀ t, MeasurableSet[m t] {ω | τ ω = t} := by
    intro t
    by_cases ht : t ∈ S
    · exact hτ t ht
    · have e : {ω | τ ω = t} = ∅ := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        intro e; exact ht (e ▸ hS ω)
      rw [e]; exact @MeasurableSet.empty Ω (m t)
  have hA0 : ∀ t, MeasurableSet {ω | τ ω = t} := fun t => hW.le t _ (hτ' t)
  have hrep : ∀ t ∈ S, Rep hW T ((memLp_oneA_mul (hA0 t) (d t)).toLp _)
      ((memLp_oneA_mulT (hA0 t) ((memLp_tl (Lp.memLp a) t).toLp _)).toLp _) := fun t ht =>
    L0 hW T (hST t ht) (hτ' t) (hd t) (tl_vanish a t) (memLp_oneA_mul (hA0 t) (d t)).coeFn_toLp
      (memLp_oneA_mulT (hA0 t) _).coeFn_toLp
  have hsum := rep_sum hW T S (θ := fun t => (memLp_oneA_mul (hA0 t) (d t)).toLp _)
    (b := fun t => (memLp_oneA_mulT (hA0 t) ((memLp_tl (Lp.memLp a) t).toLp _)).toLp _) hrep
  have hbeq : (∑ t ∈ S, (memLp_oneA_mulT (hA0 t) ((memLp_tl (Lp.memLp a) t).toLp _)).toLp _) =
      bc := by
    refine Lp.ext ?_
    filter_upwards [coeFn_fsum S
        (fun t => (memLp_oneA_mulT (hA0 t) ((memLp_tl (Lp.memLp a) t).toLp _)).toLp _),
      hbc, ae_fst_Ico (P := P) T,
      (Filter.eventually_all_finset S).2 fun t _ =>
        (memLp_oneA_mulT (hA0 t) ((memLp_tl (Lp.memLp a) t).toLp _)).coeFn_toLp,
      (Filter.eventually_all_finset S).2 fun t _ => (memLp_tl (Lp.memLp a) t).coeFn_toLp]
      with z h1 h2 h3 h4 h5
    have e : ∀ t ∈ S, ((memLp_oneA_mulT (hA0 t) ((memLp_tl (Lp.memLp a) t).toLp _)).toLp _ :
        ℝ × Ω → ℝ) z = oneA {ω | τ ω = t} z.2 * (a z * (1 - ind 0 t z.1)) := fun t ht => by
      rw [h4 t ht, h5 t ht]
    rw [h1, h2, Finset.sum_congr rfl e, Finset.sum_eq_single (τ z.2)]
    · simp only [oneA, Set.indicator_apply, Set.mem_setOf_eq, if_true, one_mul]
      by_cases hle : (τ z.2 : ℝ) ≤ z.1
      · have : ind 0 (τ z.2) z.1 = 0 := by simp [ind, Set.indicator_apply, not_lt.2 hle]
        simp [hle, this]
      · have : ind 0 (τ z.2) z.1 = 1 := by
          simp [ind, Set.indicator_apply, h3.1, lt_of_not_ge hle]
        simp [hle, this]
    · intro t _ ht
      simp only [oneA, Set.indicator_apply, Set.mem_setOf_eq]
      rw [if_neg (Ne.symm ht)]; ring
    · intro hn; exact absurd (hS z.2) hn
  exact ⟨_, by rw [← hbeq]; exact hsum⟩

theorem L2 (hW : IncrHyp m W P) (T : ℝ≥0) {θ : Lp ℝ 2 P} {a : Lp ℝ 2 (μT P T)}
    (h : Rep hW T θ a) {τ : Ω → ℝ≥0} (hτT : ∀ ω, τ ω ≤ T)
    (hτ : ∀ s, MeasurableSet[m s] {ω | τ ω ≤ s})
    {δ : Lp ℝ 2 P} {bc : Lp ℝ 2 (μT P T)}
    (hbc : bc =ᵐ[μT P T] fun z => (if (τ z.2 : ℝ) ≤ z.1 then (1 : ℝ) else 0) * a z)
    (hδ : Rep hW T δ bc) (u : ℝ≥0) {ξ : Ω → ℝ} (hξ : Measurable[m u] ξ) {C : ℝ}
    (hC : ∀ ω, |ξ ω| ≤ C) :
    ∫ ω, δ ω * (ξ ω * (if u < τ ω then (1 : ℝ) else 0)) ∂P = 0 := by
  classical
  have hst : ∀ n s, MeasurableSet[m s] {ω | gc T n (τ ω) ≤ s} := fun n => gc_stop hW.mono hτ n
  have hτm : Measurable τ := measurable_of_Iic fun x => hW.le x _ (hτ x)
  have hτnm : ∀ n, Measurable fun ω => gc T n (τ ω) := fun n =>
    measurable_of_Iic fun x => hW.le x _ (hst n x)
  have hind : ∀ σ : Ω → ℝ≥0, Measurable σ →
      Measurable fun z : ℝ × Ω => (if (σ z.2 : ℝ) ≤ z.1 then (1 : ℝ) else 0) := fun σ hσ =>
    Measurable.ite (measurableSet_le (hσ.comp measurable_snd).coe_nnreal_real measurable_fst)
      measurable_const measurable_const
  have hmem : ∀ σ : Ω → ℝ≥0, Measurable σ →
      MemLp (fun z => (if (σ z.2 : ℝ) ≤ z.1 then (1 : ℝ) else 0) * a z) 2 (μT P T) := by
    intro σ hσ
    refine (Lp.memLp a).of_le ((hind σ hσ).aestronglyMeasurable.mul (Lp.memLp a).aestronglyMeasurable)
      (Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
    refine mul_le_of_le_one_left (abs_nonneg _) ?_
    split_ifs <;> simp
  have hex : ∀ n, ∃ d : Lp ℝ 2 P, Rep hW T d ((hmem _ (hτnm n)).toLp _) := fun n =>
    L1ex hW T h.2.1 (gcS T n) (fun ω => gc_mem n (hτT ω)) (fun t ht => gcS_le ht)
      (fun t _ => eq_meas_of_stop hW.mono _ (fun ω => gc_mem n (hτT ω)) (hst n) t)
      (hmem _ (hτnm n)).coeFn_toLp
  choose d hd using hex
  have hbc0 := hmem τ hτm
  have hconv : Tendsto d atTop (𝓝 δ) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have e : ∀ n, ‖d n - δ‖ = ‖((hmem _ (hτnm n)).sub hbc0).toLp _‖ := by
      intro n
      rw [rep_norm hW T (rep_sub hW T (hd n) hδ)]
      congr 1
      refine Lp.ext ?_
      filter_upwards [Lp.coeFn_sub ((hmem _ (hτnm n)).toLp _) bc, (hmem _ (hτnm n)).coeFn_toLp,
        hbc, ((hmem _ (hτnm n)).sub hbc0).coeFn_toLp] with z h1 h2 h3 h4
      rw [h1, Pi.sub_apply, h2, h3, h4, Pi.sub_apply]
    simp_rw [e]
    have hsq : Tendsto (fun n => ‖((hmem _ (hτnm n)).sub hbc0).toLp _‖ ^ 2) atTop (𝓝 0) := by
      simp_rw [sq_norm_toLp]
      have hD : Tendsto (fun n => ∫ z, ((fun z => (if ((gc T n (τ z.2) : ℝ≥0) : ℝ) ≤ z.1 then
          (1 : ℝ) else 0) * a z) - (fun z => (if ((τ z.2 : ℝ≥0) : ℝ) ≤ z.1 then (1 : ℝ) else 0) *
          a z)) z ^ 2 ∂(μT P T)) atTop (𝓝 (∫ z, (0 : ℝ) ∂(μT P T))) := by
        refine tendsto_integral_of_dominated_convergence (fun z => a z ^ 2) (fun n => ?_)
          ((Lp.memLp a).integrable_sq) (fun n => Eventually.of_forall fun z => ?_) ?_
        · exact ((hmem _ (hτnm n)).sub hbc0).aestronglyMeasurable.pow 2
        · simp only [Pi.sub_apply, Real.norm_eq_abs]
          rw [← sub_mul, mul_pow, abs_of_nonneg (by positivity)]
          refine mul_le_of_le_one_left (sq_nonneg _) ?_
          split_ifs <;> norm_num
        · filter_upwards [ae_ne_graph (P := P) T hτm] with z hz
          refine tendsto_const_nhds.congr' ?_
          rcases lt_or_gt_of_ne hz with hlt | hgt
          · refine Eventually.of_forall fun n => ?_
            have h1 : ¬ ((gc T n (τ z.2) : ℝ≥0) : ℝ) ≤ z.1 :=
              not_le.2 (lt_of_lt_of_le hlt (by exact_mod_cast le_gc n (hτT z.2)))
            have h2 : ¬ ((τ z.2 : ℝ≥0) : ℝ) ≤ z.1 := not_le.2 hlt
            simp [h1, h2]
          · filter_upwards [(gc_tendsto (hτT z.2)).eventually (gt_mem_nhds hgt)] with n hn
            have h1 : ((gc T n (τ z.2) : ℝ≥0) : ℝ) ≤ z.1 := hn.le
            have h2 : ((τ z.2 : ℝ≥0) : ℝ) ≤ z.1 := hgt.le
            simp [h1, h2]
      rw [integral_zero] at hD
      exact hD
    have := hsq.sqrt
    simpa [Real.sqrt_sq (norm_nonneg _)] using this
  have hlt : MeasurableSet[m u] {ω | u < τ ω} := by
    have e : {ω | u < τ ω} = {ω | τ ω ≤ u}ᶜ := by ext ω; simp
    rw [e]; exact (hτ u).compl
  have hξ' : Measurable[m u] fun ω => ξ ω * (if u < τ ω then (1 : ℝ) else 0) :=
    hξ.mul (Measurable.ite hlt measurable_const measurable_const)
  have hC' : ∀ ω, |ξ ω * (if u < τ ω then (1 : ℝ) else 0)| ≤ C := fun ω => by
    rw [abs_mul]
    refine (mul_le_of_le_one_right (abs_nonneg _) ?_).trans (hC ω)
    split_ifs <;> simp
  have hz : ∀ n, ∫ ω, d n ω * (ξ ω * (if u < τ ω then (1 : ℝ) else 0)) ∂P = 0 := by
    intro n
    have h0 := L1 hW T h (gcS T n) (fun ω => gc_mem n (hτT ω)) (fun t ht => gcS_le ht)
      (fun t _ => eq_meas_of_stop hW.mono _ (fun ω => gc_mem n (hτT ω)) (hst n) t)
      (hmem _ (hτnm n)).coeFn_toLp (hd n) u hξ' hC'
    refine Eq.trans ?_ h0
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    by_cases hu : u < τ ω
    · have hu' : u < gc T n (τ ω) := lt_of_lt_of_le hu (le_gc n (hτT ω))
      simp [hu, hu']
    · simp [hu]
  have hζ2 : MemLp (fun ω => ξ ω * (if u < τ ω then (1 : ℝ) else 0)) 2 P :=
    MemLp.of_bound ((hξ'.mono (hW.le u) le_rfl).aestronglyMeasurable) C
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hC' ω)
  have hlim : Tendsto (fun n => ∫ ω, d n ω * (ξ ω * (if u < τ ω then (1 : ℝ) else 0)) ∂P) atTop
      (𝓝 (∫ ω, δ ω * (ξ ω * (if u < τ ω then (1 : ℝ) else 0)) ∂P)) := by
    simp_rw [int_eq_inner _ hζ2]
    exact hconv.inner tendsto_const_nhds
  simp_rw [hz] at hlim
  exact (tendsto_nhds_unique tendsto_const_nhds hlim).symm

end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}

lemma stop_meas (hle : ∀ t, m t ≤ mΩ) {τ : Ω → ℝ≥0} (hτ : ∀ s, MeasurableSet[m s] {ω | τ ω ≤ s}) :
    Measurable τ := measurable_of_Iic fun x => hle x _ (hτ x)

lemma gc_meas (hle : ∀ t, m t ≤ mΩ) (hmono : Monotone m) (T : ℝ≥0) {τ : Ω → ℝ≥0}
    (hτ : ∀ s, MeasurableSet[m s] {ω | τ ω ≤ s}) (n : ℕ) : Measurable fun ω => gc T n (τ ω) :=
  measurable_of_Iic fun x => hle x _ (gc_stop hmono hτ n x)

lemma memLp_stopc {T : ℝ≥0} (a : Lp ℝ 2 (μT P T)) {σ : Ω → ℝ≥0} (hσ : Measurable σ) :
    MemLp (fun z => (if (σ z.2 : ℝ) ≤ z.1 then (1 : ℝ) else 0) * a z) 2 (μT P T) := by
  have hind : Measurable fun z : ℝ × Ω => (if (σ z.2 : ℝ) ≤ z.1 then (1 : ℝ) else 0) :=
    Measurable.ite (measurableSet_le (hσ.comp measurable_snd).coe_nnreal_real measurable_fst)
      measurable_const measurable_const
  refine (Lp.memLp a).of_le (hind.aestronglyMeasurable.mul (Lp.memLp a).aestronglyMeasurable)
    (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
  refine mul_le_of_le_one_left (abs_nonneg _) ?_
  split_ifs <;> simp

lemma stopc_tendsto (hle : ∀ t, m t ≤ mΩ) (hmono : Monotone m) {T : ℝ≥0} (a : Lp ℝ 2 (μT P T))
    {τ : Ω → ℝ≥0} (hτT : ∀ ω, τ ω ≤ T) (hτ : ∀ s, MeasurableSet[m s] {ω | τ ω ≤ s}) :
    Tendsto (fun n => (memLp_stopc a (gc_meas hle hmono T hτ n)).toLp _) atTop
      (𝓝 ((memLp_stopc a (stop_meas hle hτ)).toLp _)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have e : ∀ n, ‖(memLp_stopc a (gc_meas hle hmono T hτ n)).toLp _ -
      (memLp_stopc a (stop_meas hle hτ)).toLp _‖ =
      ‖((memLp_stopc a (gc_meas hle hmono T hτ n)).sub (memLp_stopc a (stop_meas hle hτ))).toLp _‖ := by
    intro n
    congr 1
  simp_rw [e]
  have hsq : Tendsto (fun n => ‖((memLp_stopc a (gc_meas hle hmono T hτ n)).sub
      (memLp_stopc a (stop_meas hle hτ))).toLp _‖ ^ 2) atTop (𝓝 0) := by
    simp_rw [sq_norm_toLp]
    have hD : Tendsto (fun n => ∫ z, ((fun z => (if ((gc T n (τ z.2) : ℝ≥0) : ℝ) ≤ z.1 then
        (1 : ℝ) else 0) * a z) - (fun z => (if ((τ z.2 : ℝ≥0) : ℝ) ≤ z.1 then (1 : ℝ) else 0) *
        a z)) z ^ 2 ∂(μT P T)) atTop (𝓝 (∫ z, (0 : ℝ) ∂(μT P T))) := by
      refine tendsto_integral_of_dominated_convergence (fun z => a z ^ 2) (fun n => ?_)
        ((Lp.memLp a).integrable_sq) (fun n => Eventually.of_forall fun z => ?_) ?_
      · exact ((memLp_stopc a (gc_meas hle hmono T hτ n)).sub (memLp_stopc a (stop_meas hle hτ))).aestronglyMeasurable.pow 2
      · simp only [Pi.sub_apply, Real.norm_eq_abs]
        rw [← sub_mul, mul_pow, abs_of_nonneg (by positivity)]
        refine mul_le_of_le_one_left (sq_nonneg _) ?_
        split_ifs <;> norm_num
      · filter_upwards [ae_ne_graph (P := P) T (stop_meas hle hτ)] with z hz
        refine tendsto_const_nhds.congr' ?_
        rcases lt_or_gt_of_ne hz with hlt | hgt
        · refine Eventually.of_forall fun n => ?_
          have h1 : ¬ ((gc T n (τ z.2) : ℝ≥0) : ℝ) ≤ z.1 :=
            not_le.2 (lt_of_lt_of_le hlt (by exact_mod_cast le_gc n (hτT z.2)))
          have h2 : ¬ ((τ z.2 : ℝ≥0) : ℝ) ≤ z.1 := not_le.2 hlt
          simp [h1, h2]
        · filter_upwards [(gc_tendsto (hτT z.2)).eventually (gt_mem_nhds hgt)] with n hn
          have h1 : ((gc T n (τ z.2) : ℝ≥0) : ℝ) ≤ z.1 := hn.le
          have h2 : ((τ z.2 : ℝ≥0) : ℝ) ≤ z.1 := hgt.le
          simp [h1, h2]
    rw [integral_zero] at hD
    exact hD
  have := hsq.sqrt
  simpa [Real.sqrt_sq (norm_nonneg _)] using this

/-- L2 with existence: `1_{τ ≤ r} a` is an integrand, and its integral `δ` satisfies
`δ ⊥ ξ 1_{u < τ}` for bounded `m u`-measurable `ξ`. -/
theorem L2full (hW : IncrHyp m W P) (T : ℝ≥0) {θ : Lp ℝ 2 P} {a : Lp ℝ 2 (μT P T)}
    (h : Rep hW T θ a) {τ : Ω → ℝ≥0} (hτT : ∀ ω, τ ω ≤ T)
    (hτ : ∀ s, MeasurableSet[m s] {ω | τ ω ≤ s}) {bc : Lp ℝ 2 (μT P T)}
    (hbc : bc =ᵐ[μT P T] fun z => (if (τ z.2 : ℝ) ≤ z.1 then (1 : ℝ) else 0) * a z) :
    ∃ δ, Rep hW T δ bc ∧ ∀ (u : ℝ≥0) (ξ : Ω → ℝ), Measurable[m u] ξ → ∀ C : ℝ,
      (∀ ω, |ξ ω| ≤ C) → ∫ ω, δ ω * (ξ ω * (if u < τ ω then (1 : ℝ) else 0)) ∂P = 0 := by
  classical
  have hbcn := stopc_tendsto hW.le hW.mono a hτT hτ
  have hP : ∀ n, (memLp_stopc a (gc_meas hW.le hW.mono T hτ n)).toLp _ ∈
      closure (Set.range (eL (P := P) hW.le T)) := by
    intro n
    obtain ⟨d, hd⟩ := L1ex hW T h.2.1 (gcS T n) (fun ω => gc_mem n (hτT ω)) (fun t ht => gcS_le ht)
      (fun t _ => eq_meas_of_stop hW.mono _ (fun ω => gc_mem n (hτT ω)) (gc_stop hW.mono hτ n) t)
      (memLp_stopc a (gc_meas hW.le hW.mono T hτ n)).coeFn_toLp
    exact hd.2.1
  have hbc' : bc = (memLp_stopc a (stop_meas hW.le hτ)).toLp _ :=
    Lp.ext (hbc.trans (memLp_stopc a (stop_meas hW.le hτ)).coeFn_toLp.symm)
  have hbcP : bc ∈ closure (Set.range (eL (P := P) hW.le T)) := by
    rw [hbc']; exact isClosed_closure.mem_of_tendsto hbcn (Eventually.of_forall hP)
  obtain ⟨δ, hδ⟩ := rep_exists hW T hbcP
  exact ⟨δ, hδ, fun u ξ hξ C hC => L2 hW T h hτT hτ hbc hδ u hξ hC⟩

end StochCalcO3

/-! (B1) cutting a predictable integrand at a stopping time keeps it predictable. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}





end StochCalcO3
-- O7B2 tail (8c066573 relay 24): append after probe/8c066573_B.lean (= L0.lean + O7B_tail).

/-! (B2) the cut-off integral `δ = I(1_{τ ≤ r} a)` is orthogonal to `1_{r<τ} ψ`, and
(B3) the projections of `θ` and of `θ - δ` agree before `τ`. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}






end StochCalcO3

/-! O7.1 (U1, general): energy uniqueness for `a = -η c` with `η` continuous adapted. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}



end StochCalcO3

/-! O7.2 (8c066573 relay 25): K-projection.  Two filtrations `mK ≤ mF` for which the same process
`W` satisfies `IncrHyp`, plus the conditional-independence hypothesis
`H1 : E[Y | mK T] = E[Y | mK u]` for bounded `mF u`-measurable `Y` (`u ≤ T`).  If `θ = I_F(a)`
then `φ = E[θ | mK T]` is a K-stochastic integral `I_K(b)`, where `b` is the orthogonal projection
of `a` onto the K-predictable subspace: `⟪b, ψ⟫ = ⟪a, ψ⟫` for every K-predictable `ψ`. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {W : ℝ≥0 → Ω → ℝ}












end StochCalcO3

/-! O7.4a (8c066573 relay 25): identification of an integrand from localized weak pairings.
If `b, c'` are predictable and `⟪b, 1_{r<τ_R} e⟫ = -⟪c', η 1_{r<τ_R} e⟫` for every elementary `e`
and every hitting level `R ∈ ℕ` of the continuous adapted `η`, then `b = -η c'` a.e.  (This turns the
K-projection `Kproj` of `a = -η c` into the hypothesis `hac` of `U1` without assuming `η` bounded.) -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω}






end StochCalcO3

/-! O7.4b (8c066573 relay 25): `Kshift`.  If `θ = I_F(a)` with `a = -η c`, `c` the F-projection of
`θ`, and `η` continuous and K-adapted, then `φ = E[θ | mK T]` satisfies `φ = I_K(b)` with
`b = -η c_φ`, `c_φ` the K-projection of `φ` (the hypothesis shape of `U1` in the filtration K). -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {W : ℝ≥0 → Ω → ℝ}




end StochCalcO3

/-! O7.4c (8c066573 relay 25): `U1_diff` -- two integrals `θ₁ = I(-η c₁)`, `θ₂ = I(-η c₂)` (each `cᵢ`
the predictable projection of `θᵢ`, integrands vanishing before `v`) coincide.  O7.4 applies it in
the filtration K to `θ₁ = E[f | K_T] - f_t` (from `Kshift`) and `θ₂ = f_t (Z_T / Z_t - 1)` (from O7.3). -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}


end StochCalcO3

/-! O7.3 generic part (Z1): `Rep` is closed under `L²` limits of integrands (`rep_of_tendsto`),
and the truncation limit `rep_trunc`: integrands `1_{S n} f` (`S n` increasing, covering a.e.)
with `Rep θ_n (1_{S n} f)` and `‖θ_n‖ ≤ C` force `f ∈ L²(μT)` and `Rep θ f` for the `L²`
limit `θ` of `θ_n`.  Used for `Z_T - 1 = I(-Z η)` from the stopped identities. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}




end StochCalcO3

/-! Z6 (8c066573 relay 27, O7.3): L² optional-sampling bound for a right-continuous martingale
closed by `Z T`: `‖Z_{τ∧T}‖₂ ≤ ‖Z_T‖₂` for every stopping time `τ`.  Finite-valued case by
conditional Jensen on `{σ = t} ∈ m t` (`eLpNorm_condExp_le_eLpNorm`), general case by the
dyadic ceilings `gc T n τ ↓ τ ∧ T` and Fatou. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω}









end StochCalcO3

/-! Z4 (8c066573 relay 27, O7.3): Rep form of an EK Ito integral of a bounded integrand
(copy of O4step's approximation argument ending in `rep_exists`/`rep_conv`). -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology EthierKurtz ItoLib
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}



end StochCalcO3

/-! Z4t (8c066573 relay 27, O7.3): transfer of `Rep` from a larger filtration `m'` (e.g. the completed
Brownian past) to a smaller one `m ≤ m'` (e.g. `M.F`) when every `m' t`-measurable variable has an
a.e.-equal `m t`-measurable version: the elementary integrals and time-space classes agree. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {W : ℝ≥0 → Ω → ℝ}




end StochCalcO3

/-! Z5 (8c066573 relay 28, O7.3): stopped identification.  If `Rep θ a` and `K t =ᵐ E[θ | m t]`
(t ≤ T) with right-continuous paths, then for a stopping time `τ ≤ T` the variable `K_τ` is the
integral of `1_{s<τ} a`.  Route: (rep_aesm) integrals of integrands vanishing after `s` are
`m s`-measurable; (rep_ce) `E[θ|m t]` integrates `1_{s<t} a`; (Z5fin) finite-valued `τ` via `L0`;
(Z5) grid `gc T n τ ↓ τ`, `L²` limit + a.e. subsequence + right-continuity. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}








end StochCalcO3

/-! Z4m-a (8c066573 relay 28, O7.3): completed-Brownian-past measurable variables have
`M.F t`-measurable a.e. versions (append after Br.lean; needs `import Solutions.Sol_pv_1558a108`
for `ItoLib.aeClosure` / `completedBrownianPast_const_le`). -/

namespace StochCalcZ4m

open MeasureTheory ProbabilityTheory Filter HedgePSNV EthierKurtz ItoLib StochCalcBr
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

section Gen
variable {Ω' : Type*}



end Gen






end StochCalcZ4m

/-! Z4m-b (8c066573 relay 29, O7.3): a bounded library Ito integral (filtration `cBP`, driver
`W · · 0`) of the HedgePSNV model is represented (`Rep`, filtration `M.F`, driver `M.B`) by its
integrand.  `M.F`-measurable a.e. versions of the library approximants (hmod_cBP), clamped to keep
the per-level bounds, then `StochCalcO3.O4rep`. Append after the combined dev base (O6M + generic
Z chain + O7Z4m_tail). -/

namespace StochCalcZ4mb

open MeasureTheory ProbabilityTheory Filter HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcO3 StochCalcO3M StochCalcZ4m
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]



end StochCalcZ4mb


/-! Z2 (8c066573 relay 29, O7.3): a continuous, `cBP`-adapted version `Ic` of the Ito integral of
`η' s = η (s ∧ T)`, glued from the continuous Ito integrals of the clamped integrands `clamp n η'`
(platform theorem 1c98c8e0, conjunct 3, as the hypothesis `ContHyp M`).  Gluing index: the least
`n` with `sup |η'| ≤ n` (whole horizon) for the paths, and the least `n` with `sup_{[0,t]} |η'| ≤ n`
for the `cBP t`-measurable version at time `t` (completeness of `cBP t`).  Append after
O7Z4mb_tail. -/

namespace StochCalcZ2

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

















end StochCalcZ2



/-! Z3 (8c066573 relay 29, O7.3): Ito formula for `Zc = exp(-Ic - ½∫η'²)`: for a continuous,
`cBP`-adapted Ito integral `Ic` of `η'` (Z2), `Zc t = 1 + K t` a.s. for each `t`, where `K` is the
Ito integral of `-Zc η'` (ItoLib `ito_formula` with `e = 1`, `X = Ic + ½∫η'²`, `f x = exp(-x₀)`).
Append after O7Z2_tail. -/

namespace StochCalcZ3

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW StochCalcZ2
open scoped NNReal ENNReal

section line
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]





end line

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]












end StochCalcZ3

/-! Z7a (8c066573 relay 30, O7.3): horizon change for `Rep` (an integrand on `[0,t)` represents
the same variable at any later horizon `T`), hence the conditional expectation of a represented
variable at time `t` is represented at horizon `t`; model corollary `Jmart`: a bounded library Ito
integral is an `M.F`-martingale.  Append after O7Z3_tail. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}













end StochCalcO3

namespace StochCalcZ7a

open MeasureTheory ProbabilityTheory Filter HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcO3 StochCalcO3M StochCalcZ4m StochCalcZ4mb
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]


end StochCalcZ7a

/-! Z7b/Z7c (8c066573 relay 30, O7.3): `Zc` is continuous, `M.F`-adapted, a.e. equal to `M.Z`
on `[0,T]` and an `M.F`-martingale closed by `Zc T` (Assumption5); stopping at the hitting time
`τ R` of `|Zc η'| ≥ R`, the library Ito integral `J` of the clamped integrand `Hcl R` equals
`Zc - 1` at `τ R` (locality at dyadic `t < τ R` + path continuity).  Append after O7Z7a_tail. -/

namespace StochCalcZ7b

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW StochCalcZ2 StochCalcZ3 StochCalcZ4m StochCalcHit
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]






variable {Ic : ℝ≥0 → Ω → ℝ}
















end StochCalcZ7b

/-! Z7d (8c066573 relay 30, O7.3 assembly): `Zc T - 1` is represented (`Rep`, filtration `M.F`,
driver `M.B`) by the integrand `-Zc η'` on `[0,T)`, which is in `L²(dt × dP)`.  Per level `n`:
ContHyp integral `J n` of `Hcl n`, Z4m representative, Jmart (Z5's martingale hypothesis), Z5 at
`tau n`, locality `loc`, Z6 bound; then rep_trunc over `S n = {s < tau n}` and the a.e. limit
(`tau n = T` eventually).  Append after O7Z7b_tail. -/

namespace StochCalcZ7d

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW StochCalcZ2 StochCalcZ3 StochCalcZ4m StochCalcZ4mb StochCalcHit
open StochCalcO3 StochCalcO3M StochCalcZ7a StochCalcZ7b
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]



end StochCalcZ7d


/-! O7ZM (8c066573 relay 31, O7.3 remainder): multiplication of a stochastic integral by a
bounded `m t`-measurable factor `ζ` (generalizes `L0`, where `ζ = 1_A`), and the tail
representation `θ - E[θ | m t] = I(a 1_[t,T))`.  Generic `StochCalcO3`; append after O7Z7d. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}












end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω}








end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}


end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]


end StochCalcO3

/-! O7ZK (8c066573 relay 32, O7.3 model instance in a sub-filtration `mK`): generic
`rep_restrict` (an `mF`-representation of an `mK T`-measurable `θ` by an `mK`-predictable integrand
is an `mK`-representation), `mart_restrict` (tower property), and the model instance `zK` of `ztail`
for `ZT = Zc (· ∧ T)` in any filtration `cBP ≤ mK ≤ M.F` with `IncrHyp mK M.B` and `H1`.
Generic `StochCalcO3` part + `StochCalcZK`; append after O7ZM_tail. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {W : ℝ≥0 → Ω → ℝ}




end StochCalcO3

namespace StochCalcZK

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW StochCalcZ2 StochCalcZ3 StochCalcZ4m StochCalcZ4mb StochCalcHit
open StochCalcO3 StochCalcO3M StochCalcZ7a StochCalcZ7b StochCalcZ7d
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]




end StochCalcZK

/-! O7KF (8c066573 relay 32, model K + H1 for O7.4): the filtration
`Kf t s = F_s (s < t), F_t ⊔ G_s (s ≥ t)`, with `Kf ≤ F`, `IncrHyp (Kf t) M.B`, `Zc` and `η`
`Kf`-adapted on `[0,T]`, and the conditional-independence hypothesis `H1` of `Kproj`/`Kshift`.
Generic part: `ce_sup_indep` (`E[Y | A ⊔ D] = E[Y | A]` for `Y ∈ F' ⊇ A`, `F' ⊥ D`) and
`meas_of_ae_eq_nulls`.  Append after O7ZK_tail. -/

namespace StochCalcCE

open MeasureTheory ProbabilityTheory Filter

variable {Ω : Type*} {A F' D K : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]




end StochCalcCE

namespace StochCalcKF

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW StochCalcZ2 StochCalcZ3 StochCalcZ4m StochCalcZ4mb StochCalcHit
open StochCalcO3 StochCalcO3M StochCalcZ7a StochCalcZ7b StochCalcZ7d StochCalcCE StochCalcR1M
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

















end StochCalcKF

/-! O7Q1 (8c066573 relay 32, O7.4 generic core): if `θ = I_F(a)` with `a = -η c` (`c` the
F-projection of `θ`, `η` continuous `mK`-adapted) and `Θ = E[θ | mK T]` is orthogonal to `L∞(mK t)`,
then `Θ = 0`.  Kshift (Θ = I_K(-η cΘ)), perp_tail (cΘ = 0 before t), U1.  Append after O7KF_tail. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {W : ℝ≥0 → Ω → ℝ}


end StochCalcO3

/-! O7Q1M (8c066573 relay 33, O7.4 model): `E[θ | F_t ⊔ G_T] = E[θ|F_t] Z_T / Z_t` for `θ = I_F(-η c)`.
Generic: `int_mul_ce`, `proj_tailA` (F-projection of `1_A (θ - f_t)`).  Model: `Q1R` (fixed `R`), `Q1model`.
Append after O7Q1_tail. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]


variable {m : ℝ≥0 → MeasurableSpace Ω}


end StochCalcO3

namespace StochCalcQ1M

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW StochCalcZ2 StochCalcZ3 StochCalcZ4m StochCalcZ4mb StochCalcHit
open StochCalcO3 StochCalcO3M StochCalcZ7a StochCalcZ7b StochCalcZ7d StochCalcCE StochCalcR1M
open StochCalcZK StochCalcKF
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]



end StochCalcQ1M

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal Topology


set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace StochCalcHedge

open HedgePSNV







end StochCalcHedge

/-! S8 tail (8c066573 relay 1, 2026-11-06): `0 ≤ Z_t/Z^M_t ≤ 1` a.s. and the three elementary
conjuncts of theorem_1_ii (everything except the value formula (21)).
Appended after S8.lean (namespace StochCalcHedge provides I_zero_ae, Z_pos, Z_T_measurable,
ZM0_eq, one_lt_ZM0). -/

namespace StochCalcS8b

open HedgePSNV StochCalcHedge









end StochCalcS8b
/-! K2a (8c066573 relay 2, 2026-11-06): base change `P → P^M` for the `B~`-tilt machinery.
`dP^M/dP = Z_T` is `G_T`-measurable, so every independence `F_u ⊔ G_T ⊥ (B~ increments after u)`
and the Gaussian laws of the increments survive under `P^M`; the exponential `B~`-tilts of `P^M`
are in `M_X` once `X` is a `P^M`-martingale (no L² assumption on `X`).
Append after cc6d45ce_P4.lean + S8.lean + S8b_tail.lean (imports stripped). -/

namespace StochCalcK2

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt StochCalcTiltM
  StochCalcSteinM

section generic

variable {Ω : Type*}





end generic

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]




















end StochCalcK2
/-! K2b (8c066573 relay 2): orthogonality `E^M[Y ξ χ_T] = 0` and the Stein identity under `P^M`.
Append after K2a_tail.lean. -/

namespace StochCalcK2

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt StochCalcTiltM
  StochCalcSteinM StochCalcStein StochCalcOrth

section generic

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}


end generic

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]







end StochCalcK2
/-! K2c (8c066573 relay 2): Bessel inequality for two orthogonal test variables, and the
`Z_T`-weighted martingale-difference sums `S = Σ_{k<N} Y_k ξ_k` on the grid `gr p n`
(`E_P[Z_T² S²] = Σ E_P[Z_T² Y_k²] T/n`, `E_P[Z_T² S] = E_P[Z_T S] = 0`) via the auxiliary
measure `Q2 = (Z_T²/c)·P`, under which the grid increments keep their independence and laws.
Append after K2b_tail.lean (needs D2_tail's `gr`, `V_gr`; i.e. a dev file containing D2). -/

namespace StochCalcK2

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt StochCalcTiltM
  StochCalcSteinM StochCalcP6S

section generic

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]



end generic

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]




















end StochCalcK2


/-! O7Q2 (8c066573 relay 34, O7.5 glue hQb): Bayes formula for the tilted measure
`Q = (Z²/c)·P` and the Q2 form of O7.4: with `g = θ / Z_T`,
`E_Q[g | m] = E_P[θ|F_t] / Z_t` for every `F_t ≤ m ≤ F_t ⊔ G_T`; hence
`E_Q[g | F_t ⊔ G_T] = E_Q[g | F_t]` (the `hQb` hypothesis of `StochCalcE2.E2_bound`).
Generic: `StochCalcQ2.bayes_ce`.  Model: `StochCalcQ2.Q2ce`, `StochCalcQ2.Q2_hQb`.
Append after O7Q1M_tail (inside the dev file's `namespace StochCalcP6`). -/

namespace StochCalcQ2

open MeasureTheory ProbabilityTheory Filter Topology
open StochCalcTilt
open scoped NNReal ENNReal

section generic

variable {Ω : Type*} {m mH : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]


end generic

end StochCalcQ2

namespace StochCalcQ2M

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW StochCalcZ2 StochCalcZ3 StochCalcZ4m StochCalcZ4mb StochCalcHit
open StochCalcO3 StochCalcO3M StochCalcZ7a StochCalcZ7b StochCalcZ7d StochCalcCE StochCalcR1M
open StochCalcZK StochCalcKF StochCalcTilt StochCalcQ2
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]



end StochCalcQ2M


/-! O7.5 piece (relay 21): one-cell identity of the E2 error argument (pure Mathlib).
F-filtration (F k) ≤ (F (k + 1)), enlarged H-filtration (H k) ≤ (H (k + 1)) ((F k) ≤ (H k), (F (k + 1)) ≤ (H (k + 1))), increment w ((F (k + 1))-measurable,
"independent of (H k) with mean 0" in the form `hind`), g with E[g|(H (k + 1))] = E[g|(F (k + 1))] (Q1), NC for (F k)-multipliers.
Then for a bounded (H k)-measurable y:  E[g y w] = E[(gb - ga) w (yb - ya)]. -/

set_option autoImplicit false

open MeasureTheory Filter
open scoped NNReal

namespace StochCalcE2

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]



end StochCalcE2

-- O7E3 tail (8c066573 relay 24): append after lib/stochcalc/O7E2.lean (pure Mathlib).

/-! O7.5 (E2 n-cell sum): splitting a cell into `n` pieces, the NC orthogonality gives
`|E[g y ΣΔW]| ≤ l/2 E g² + (1/2l)(μ/2 Σ E w_k⁴ + 2 Cy⁴/μ)` for all `l, μ > 0`; with `Σ E w_k⁴ = O(1/n)`
this forces `E[g y ΣΔW] = 0`. -/

namespace StochCalcE2

open MeasureTheory Filter Topology
open scoped NNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]









end StochCalcE2


/-! O7G4 (8c066573 relay 24, for the O7.5 model instance): fourth moments of centred Gaussians
scale like `v²`: `∫ x⁴ dN(0,v) = v² ∫ x⁴ dN(0,1)`, and a random variable with law `N(0,v)` has
`E w⁴ = v² K₄`, `K₄ := ∫ x⁴ dN(0,1)` (finite). Pure Mathlib. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace StochCalcG4




end StochCalcG4

/-! O7E5 (8c066573 relay 34, O7.5 model glue): under `Q2 = (Z_T²/c)·P`, if `g = f/Z_T` has the
Q1 property `E_Q2[g | F_t ⊔ G_T] = E_Q2[g | F_t]` (`StochCalcQ2M.Q2ce`) and `f` is orthogonal to
the grid class `NC` (expanded form `hfN`), then `E_Q2[g y (B~_{t_{j+1}} - B~_{t_j})] = 0` for every
bounded `F_{t_j} ⊔ G_T`-measurable `y` (cell split in `r` pieces + `StochCalcE2.E2_bound` +
`StochCalcE2.zero_of_bounds`).  Append after E2G4_block (dev base M15). -/

namespace StochCalcE5M

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV
open StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt StochCalcTiltM StochCalcSteinM StochCalcP6S
open StochCalcK2 StochCalcD2 StochCalcE2 StochCalcG4
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]




end StochCalcE5M

end StochCalcP6
-- ===== slice of P8c066573M17 (scratch/probe/slice8c/cuts/r_l2.lean.src/P8c066573M17.lean): 0/73 top-level decls kept =====

namespace StochCalcP6

set_option autoImplicit false

/-! O7E6 (8c066573 relay 35, O7.6): conclusion of the completeness argument.  Under
`Q2 = (Z_T²/c)·P`, let `g = f/Z_T`.  If `g ⊥_Q2 L∞(G_T)` (`hG`, from `Q2ce` at `t = 0`) and
`g ⊥_Q2 y·ΔB~_cell` for bounded `F_{t_j} ⊔ G_T`-measurable `y` (`hE`, the conclusion of
`StochCalcE5M.E5`), then `E_P[f Z_T ζ e^{i Σ μ_k ΔB~_k}] = 0` for bounded `G_T`-measurable `ζ`
(`StochCalcR1.core` under `Q2`: exponentials of `B~`-grid sums are `L²(Q2)`-limits of constants
plus `F_{t_l} ⊔ G_T`-weighted `B~`-grid sums), hence `f Z_T` is orthogonal to every
`cos/sin ⟪Δ_j, t⟫` (`StochCalcR5.inner_Δ`, `cos (a + b)` split with `a` the `B`-part) and
`StochCalcR2.ae_eq_zero_of_trig` gives `f Z_T = 0`, so `f = 0`.  Append after O7E5_tail (dev base M16). -/

namespace StochCalcE6M

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV Finset
open StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt StochCalcTiltM StochCalcSteinM StochCalcP6S
open StochCalcK2 StochCalcD2 StochCalcD3 StochCalcE2 StochCalcG4 StochCalcR5
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]









end StochCalcE6M

end StochCalcP6

namespace StochCalcP6

set_option autoImplicit false

/-! O7HG (8c066573 relay 36): the `hG` input of `StochCalcE6M.E6` from `Q2ce` at `t = 0`.
`F_0` (augmented natural filtration of `(B, B~)` at time `0`) is `P`-trivial since `B_0 = B~_0 = 0`
a.s., so `E_P[f | F_0] = ∫ f = 0`; `Q2ce` at `t = 0` gives `E_Q2[f/Z_T | F_0 ⊔ G_T] = 0`, hence
`∫ f/Z_T · ζ dQ2 = 0` for bounded `G_T`-measurable `ζ`.  Append after O7E5_tail (dev base M16). -/

namespace StochCalcHGM

open MeasureTheory ProbabilityTheory Filter HedgePSNV Set
open StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt StochCalcTiltM StochCalcSteinM StochCalcP6S
open StochCalcK2 StochCalcD2 StochCalcD3 StochCalcZ3
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]





end StochCalcHGM

end StochCalcP6

namespace StochCalcP6

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set EthierKurtz
open scoped ENNReal NNReal Topology BigOperators

/-! O70 support (copied from the accepted cc6d45ce library: StochCalcS2 clR + hasIto_add, StochCalcS3 hasIto_tail,
StochCalcS3M ext_hasIto, StochCalcFe). -/

namespace StochCalcS2

open ItoLib StochCalcTC StochCalcL2M

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]














end StochCalcS2
namespace StochCalcS3

open EthierKurtz ItoLib StochCalcTC StochCalcS2

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]








end StochCalcS3
namespace StochCalcS3M

open HedgePSNV EthierKurtz StochCalcBr StochCalcD1b StochCalcD1aW StochCalcTC ItoLib
  StochCalcS1M StochCalcS2 StochCalcS3

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]




end StochCalcS3M
namespace StochCalcFe

open Real

section line
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]




end line










end StochCalcFe

/-! O7.0 (8c066573 relay 36): `X_t ≠ 0` a.s. in the NON-degenerate model (no `hdeg`, no `QVStatement`):
Ito formula for `f_ε(x) = ½ log(x² + ε)` on `X` frozen at `T` and continued with its drift and
Brownian increments, localized on `σ ≤ Rσ`, `μ ≤ Rμ`; then `μT`-a.e. via Tonelli, and the `hac`
input of `Q2ce`: `a' Xσ + c Xμ = 0 ⇒ a' = -η c`. -/

namespace StochCalcX0

open MeasureTheory ProbabilityTheory Filter Set
open HedgePSNV EthierKurtz StochCalcBr StochCalcD1b StochCalcD1aW StochCalcTC ItoLib
  StochCalcS1M StochCalcS2 StochCalcS3 StochCalcS3M StochCalcFe
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]




























end StochCalcX0

end StochCalcP6

-- ===== slice of P8c066573M18 (scratch/probe/slice8c/cuts/r_l2.lean.src/P8c066573M18.lean): 0/23 top-level decls kept =====

namespace StochCalcP6

set_option autoImplicit false

/-! GQ (8c066573 relay 37): the O7.4 chain for a GENERAL `θ = θB + θ⊥` (relay 37 found that
`Q1model`/`Q2ce` assume `θ` is a pure `B`-integral, but the completeness argument applies them to `f`,
which also has a `B~`-part).  `KshiftG`/`Q1coreG`: `Rep θB a` for the `B`-part only, `hproj` for the
full `θ`, and `E[θ - θB | K_T] = 0`. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {W : ℝ≥0 → Ω → ℝ}



end StochCalcO3


namespace StochCalcQ1M

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW StochCalcZ2 StochCalcZ3 StochCalcZ4m StochCalcZ4mb StochCalcHit
open StochCalcO3 StochCalcO3M StochCalcZ7a StochCalcZ7b StochCalcZ7d StochCalcCE StochCalcR1M
open StochCalcZK StochCalcKF
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]



end StochCalcQ1M

namespace StochCalcQ2M

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW StochCalcZ2 StochCalcZ3 StochCalcZ4m StochCalcZ4mb StochCalcHit
open StochCalcO3 StochCalcO3M StochCalcZ7a StochCalcZ7b StochCalcZ7d StochCalcCE StochCalcR1M
open StochCalcZK StochCalcKF StochCalcTilt StochCalcQ2
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]


end StochCalcQ2M

end StochCalcP6

namespace StochCalcP6

set_option autoImplicit false

/-! G3/G5 (8c066573 relay 38).  G5: `O6_modelP` = `O6_model` also exporting that `a'` is
predictable (in the closure of the elementaries).  G3: for `θ` in the closure of the elementary
`B~`-integrals, `E[θ | F_t ⊔ G_T] = E[θ | F_t]` (the `B~` increments after `u` are independent of
`F_u ⊔ G_T`). -/

namespace StochCalcO6M

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1b StochCalcO3 StochCalcO3M StochCalcS1R StochCalcHit StochCalcO4M
open StochCalcO5
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]



end StochCalcO6M

namespace StochCalcG3

open MeasureTheory ProbabilityTheory Filter Topology StochCalcO3
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} {m1 m2 mG n : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]




end StochCalcG3

namespace StochCalcG3M

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV
open StochCalcO3 StochCalcO3M StochCalcKF StochCalcSteinM
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]



end StochCalcG3M


namespace StochCalcG4

open MeasureTheory ProbabilityTheory Filter Topology StochCalcO3
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]





variable {mF : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}





end StochCalcG4


namespace StochCalcG4M

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV
open StochCalcO3 StochCalcO3M StochCalcG3M StochCalcG4 StochCalcR1M StochCalcR4 StochCalcR7 StochCalcD2
  StochCalcD3 StochCalcTiltM
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]




end StochCalcG4M

end StochCalcP6

namespace StochCalcP6

set_option autoImplicit false

/-! HC (8c066573 relay 38): **M6 hcomp** (completeness) from O3_model, O6_modelP, O70, G4, G3, Z2, Z3,
Q2ceG, E5, hG_glue, E6.  `ContHyp M` (conj 3 of platform theorem 1c98c8e0) is kept as a hypothesis. -/

namespace StochCalcHC

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcO3 StochCalcO3M StochCalcO6M StochCalcG3M StochCalcG4 StochCalcG4M StochCalcKF
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]


end StochCalcHC

end StochCalcP6

-- ===== slice of __current__ (scratch/probe/slice8c/cuts/r_l2.lean.src/__current__.lean): 0/98 top-level decls kept =====

namespace StochCalcP6

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

/-! K2d (relay 3): the finite-grid lower bound under `P^M`, tests `D0 = Z_T - 1`, `D1 = Z_T S`. -/

namespace StochCalcK2

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt StochCalcTiltM

section generic

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]


end generic

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]





end StochCalcK2

/-! K2e (relay 3): the grid weights `Y = a·ĉ_t / max(Z^M_t, ε)` and the bracket bound. -/

namespace StochCalcK2

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt StochCalcTiltM

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

















end StochCalcK2

/-! K2f (relay 3): `ε ↓ 0` in the grid bound; `Z^M_t > 0` `P^M`-a.s. -/

namespace StochCalcK2

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt StochCalcTiltM
open Filter Topology

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]








end StochCalcK2

/-! K2g (relay 3): `G(u) = E_P[Z_u/Z^M_u δ_u²]`, `G` monotone and bounded. -/

namespace StochCalcK2

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt StochCalcTiltM
open Filter Topology

section generic

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}



end generic

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]






end StochCalcK2

/-! K2h (relay 3): Riemann sums and the assembled lower bound K2. -/

namespace StochCalcK2

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt StochCalcTiltM
open Filter Topology

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]







end StochCalcK2

/-! K3H (8c066573 relay 11): abstract Hilbert-space glue for the upper bound K3 of HedgePSNV.theorem_1_ii.
E = L²(F_T, P), one = 1, z = Z_T, h = H, A = admissible gains {χ_T}, N = span{Z_T γ ξ_k} (B̃-part of the
dual space).  Completeness `hcomp` (f ⊥ 1, A, N ⇒ f = 0) is the martingale-representation input. -/

set_option autoImplicit false

open scoped RealInnerProductSpace

namespace StochCalcK3H

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]





section Fn

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]



end Fn

end StochCalcK3H

/-! K3M0 (8c066573 relay 11): model-level glue.  `HedgePSNV.theorem_1_ii_upper_bound`'s conclusion from the
obligations M1-M6 of scratch/decomp/8c066573.K3plan.md, stated on `P` (F_T-measurable functions), via
`StochCalcK3H.fn_upper` on `P.trim (F_T ≤ m)`.  Append after K3H.lean (needs Definitions.Def_HedgePSNV_Hedging). -/

namespace StochCalcK3M0

open MeasureTheory ProbabilityTheory HedgePSNV
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]



end StochCalcK3M0
/-! K3M1 (8c066573 relay 12): the easy obligations of `StochCalcK3M0.K3_of_obl`:
`A_X` contains `0` and is closed under `+` and scalar multiples (linearity of the Ito relation and
of `IsMartingaleOn`), `Z_T`/`H` measurability and `L²`, `E Z_T = 1`, `1 < E Z_T²`, `V0 = E[H Z_T]`,
`E[Z_T χ_T] = 0`.  `K3_of_N` is then K3 from the `N`-class obligations, `hcomp` (M6) and `hbd` (M5).
Append after K3H + K3M0_tail (on top of the K2 dev chain probe/8c066573_K2h.lean). -/

namespace StochCalcK3M1

open MeasureTheory ProbabilityTheory Filter HedgePSNV EthierKurtz ItoLib
open scoped NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]













variable {p : Params}









end StochCalcK3M1
/-! K3M2 (8c066573 relay 12): the class `N` of `Z_T`-weighted `B~`-grid sums
`n = Z_T * Σ_{k<n} Y_k ξ(t_k, t_{k+1})` (uniform grid `t_k = k T / n` of K2, `Y_k` bounded
`F_{t_k}`-measurable) and its obligations in `StochCalcK3M1.K3_of_N`: `L²`, `F_T`-measurability,
`0`, closure under `+` (common refinement `n * n'`) and scalar multiples, orthogonality to the
gains `χ_T` (under `P^M`), to `1` and to `Z_T`.  `K3_of_M56` = K3 from M5 (`hbd`) and M6 (`hcomp`)
for this class.  Append after K3M1_tail. -/

namespace StochCalcK3M2

open MeasureTheory ProbabilityTheory Filter HedgePSNV
open StochCalcBr StochCalcGauss StochCalcTiltM StochCalcSteinM StochCalcHedge StochCalcS8b
  StochCalcK2 StochCalcD2
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]


















end StochCalcK3M2
/-! K3M5 (8c066573 relay 13): obligation M5 of `StochCalcK3M2.K3_of_M56`.  For
`f = Z_T * Σ_k Y_k ξ_k` in the grid class `NC`, `(E_P[H f])² ≤ Ψ E_P[f²]` with
`Ψ = ∫_0^T fK` (= the target `∫ E_P[(Z_u/Z^M_u) δ_u²] du`).  Proof: Stein under `P^M` turns
`E_P[H f]` into `Σ (T/n) E^M[a c^M_{t_k} Y_k]`; the tower property turns `E_P[f²]` into
`Σ (T/n) E^M[Z^M_{t_k} Y_k²]`; a weighted AM-GM bound for every `λ > 0` gives Cauchy-Schwarz;
the left Riemann sum of the monotone `fK` is below its integral.  `K3_of_M6` = K3 from M6
(`hcomp`) only.  Append after K3M2_tail. -/

namespace StochCalcK3M5

open MeasureTheory ProbabilityTheory Filter HedgePSNV
open StochCalcBr StochCalcGauss StochCalcTiltM StochCalcSteinM StochCalcHedge StochCalcS8b
  StochCalcK2 StochCalcD2 StochCalcK3M2
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]










end StochCalcK3M5

/-! K3G (8c066573 relay 39): K3 (upper bound of (21)) from `K3_of_M6` + `hcomp`, with the
continuity hypothesis `ContHyp M` (conjunct 3 of platform theorem 1c98c8e0) kept explicit. -/

namespace StochCalcK3G

open MeasureTheory ProbabilityTheory Filter HedgePSNV
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]





end StochCalcK3G

end StochCalcP6


open MeasureTheory ProbabilityTheory in
open scoped NNReal in
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → ℝ} {m : ℝ≥0 → MeasurableSpace Ω}
    (hK1 : Monotone m) (hK2 : ∀ s, m s ≤ mΩ) (hK3 : ∀ s, Measurable[m s] (W s))
    (hK4 : ∀ u v, u ≤ v →
      Indep (m u) (MeasurableSpace.comap (fun ω => W v ω - W u ω) inferInstance) P)
    (hK5 : ∀ u v, MemLp (fun ω => W v ω - W u ω) 2 P)
    (hK6 : ∀ u v, u ≤ v → ∫ ω, (W v ω - W u ω) ∂P = 0)
    (hK7 : ∀ u v, u ≤ v → ∫ ω, (W v ω - W u ω) ^ 2 ∂P = (v : ℝ) - u)
    (T : ℝ≥0) (μ : Measure (ℝ × Ω)) (hμ : μ = (volume.restrict (Set.Ico (0 : ℝ) T)).prod P)
    {θ : Lp ℝ 2 P} {a : Lp ℝ 2 μ}
    (hr1 : θ ∈ closure (Submodule.span ℝ {g : Lp ℝ 2 P | ∃ u v : ℝ≥0, u ≤ v ∧ v ≤ T ∧
          ∃ Y : Ω → ℝ, Measurable[m u] Y ∧ (∃ C : ℝ, ∀ ω, |Y ω| ≤ C) ∧
          ∃ h : MemLp (fun ω => Y ω * (W v ω - W u ω)) 2 P, g = h.toLp _} : Set (Lp ℝ 2 P)))
    (hr2 : a ∈ closure (Submodule.span ℝ {g : Lp ℝ 2 μ | ∃ u v : ℝ≥0, u ≤ v ∧ v ≤ T ∧
          ∃ Y : Ω → ℝ, Measurable[m u] Y ∧ (∃ C : ℝ, ∀ ω, |Y ω| ≤ C) ∧
          ∃ h : MemLp (fun z : ℝ × Ω => (Set.Ico (u : ℝ) v).indicator (fun _ => (1 : ℝ)) z.1 * Y z.2) 2 μ,
            g = h.toLp _} : Set (Lp ℝ 2 μ)))
    (hr3 : ∀ u v : ℝ≥0, u ≤ v → v ≤ T → ∀ Y : Ω → ℝ, Measurable[m u] Y →
        (∃ C : ℝ, ∀ ω, |Y ω| ≤ C) →
        ∫ ω, (θ : Ω → ℝ) ω * (Y ω * (W v ω - W u ω)) ∂P =
          ∫ z, (a : ℝ × Ω → ℝ) z * ((Set.Ico (u : ℝ) v).indicator (fun _ => (1 : ℝ)) z.1 * Y z.2) ∂μ)
    {τ : Ω → ℝ≥0} (hτT : ∀ ω, τ ω ≤ T)
    (hτ : ∀ s, MeasurableSet[m s] {ω | τ ω ≤ s}) {bc : Lp ℝ 2 μ}
    (hbc : bc =ᵐ[μ] fun z => (if (τ z.2 : ℝ) ≤ z.1 then (1 : ℝ) else 0) * a z) :
    ∃ δ : Lp ℝ 2 P, (δ ∈ closure (Submodule.span ℝ {g : Lp ℝ 2 P | ∃ u v : ℝ≥0, u ≤ v ∧ v ≤ T ∧
          ∃ Y : Ω → ℝ, Measurable[m u] Y ∧ (∃ C : ℝ, ∀ ω, |Y ω| ≤ C) ∧
          ∃ h : MemLp (fun ω => Y ω * (W v ω - W u ω)) 2 P, g = h.toLp _} : Set (Lp ℝ 2 P)) ∧
      bc ∈ closure (Submodule.span ℝ {g : Lp ℝ 2 μ | ∃ u v : ℝ≥0, u ≤ v ∧ v ≤ T ∧
          ∃ Y : Ω → ℝ, Measurable[m u] Y ∧ (∃ C : ℝ, ∀ ω, |Y ω| ≤ C) ∧
          ∃ h : MemLp (fun z : ℝ × Ω => (Set.Ico (u : ℝ) v).indicator (fun _ => (1 : ℝ)) z.1 * Y z.2) 2 μ,
            g = h.toLp _} : Set (Lp ℝ 2 μ)) ∧
      ∀ u v : ℝ≥0, u ≤ v → v ≤ T → ∀ Y : Ω → ℝ, Measurable[m u] Y →
        (∃ C : ℝ, ∀ ω, |Y ω| ≤ C) →
        ∫ ω, (δ : Ω → ℝ) ω * (Y ω * (W v ω - W u ω)) ∂P =
          ∫ z, (bc : ℝ × Ω → ℝ) z * ((Set.Ico (u : ℝ) v).indicator (fun _ => (1 : ℝ)) z.1 * Y z.2) ∂μ) ∧
      ∀ (u : ℝ≥0) (ξ : Ω → ℝ), Measurable[m u] ξ → ∀ C : ℝ,
        (∀ ω, |ξ ω| ≤ C) → ∫ ω, δ ω * (ξ ω * (if u < τ ω then (1 : ℝ) else 0)) ∂P = 0 := by
  subst hμ
  have hW : StochCalcP6.StochCalcO3.IncrHyp m W P := ⟨hK1, hK2, hK3, hK4, hK5, hK6, hK7⟩
  obtain ⟨δ, hδ, h2⟩ := StochCalcP6.StochCalcO3.L2full hW T
    ((StochCalcP6.StochCalcRU.rep_iff hW T θ a).2 (by unfold StochCalcP6.StochCalcRU.RepU; exact ⟨hr1, hr2, hr3⟩)) hτT hτ hbc
  have h1 := (StochCalcP6.StochCalcRU.rep_iff hW T δ bc).1 hδ
  unfold StochCalcP6.StochCalcRU.RepU at h1
  exact ⟨δ, h1, h2⟩
