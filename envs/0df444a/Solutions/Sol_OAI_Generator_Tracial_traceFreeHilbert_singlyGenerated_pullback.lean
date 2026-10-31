-- Prove2me | solution 1 for OAI.Generator.Tracial.traceFreeHilbert_singlyGenerated_pullback
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T16:56:11.01798+00:00
-- url     : https://prove2.me/submissions/5685d1cb-e8b4-44f9-a252-8288838a2ef5

import Mathlib
import Definitions.Def_FactorGeneration
import Definitions.Def_OAIQ11Fg019

section
-- module Solutions.OAIQ11_FG.FactorGeneration_Target
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

namespace Generator

/-! Weak operator generation of concrete finite diffuse factors with separable Banach preduals. -/
noncomputable section
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem wstar_le {s : Set (H →L[ℂ] H)} {S : StarSubalgebra ℂ (H →L[ℂ] H)}
    (hS : WOTClosed S) (hs : s ⊆ S) : wstar s ≤ S :=
  sInf_le ⟨hS, hs⟩

end

end Generator

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_TraceTransport
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.quotientInnerProductSpace _root_.OAI.Generator.Tracial.quotientNormedAddCommGroup _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.Tracial.sequencesIsTopologicalRing _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator

/-! Literal weak-operator generation under a concrete star-algebra isomorphism.
Continuity is explicitly for the restricted WOT, not the operator norm topology.
This transport does not construct a trace representation of a finite factor. -/

/-! Compact original image balls and spectral clipping identify the actual
bicommutant with the original algebra's represented image. -/
open Filter
open scoped ComplexConjugate ComplexStarModule CStarAlgebra Pointwise Topology
namespace Tracial

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)

local notation "K" => TraceFreeHilbert hfactor hdiff hfinite hunit

local notation "N" => traceFreeHilbertClosure hfactor hdiff hfinite hunit

theorem traceHilbertVonNeumann_wotClosed {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]
    (P : VonNeumannAlgebra J) : WOTClosed P.toStarSubalgebra := by
  change IsClosed {T : J →WOT[ℂ] J | T.toCLM ∈ (P : Set (J →L[ℂ] J))}
  rw [← P.centralizer_centralizer]
  change IsClosed {T : J →WOT[ℂ] J |
    ∀ S ∈ Set.centralizer (P : Set (J →L[ℂ] J)),S*T.toCLM=T.toCLM*S}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro S
  apply isClosed_iInter
  intro hS
  have he : {T : J →WOT[ℂ] J | S*T.toCLM=T.toCLM*S} =
      {T : J →WOT[ℂ] J |
        (ContinuousLinearMapWOT.equiv.symm S)*T=T*(ContinuousLinearMapWOT.equiv.symm S)} := by
    ext T
    let e : (J →WOT[ℂ] J) ≃ (J →L[ℂ] J) := ContinuousLinearMapWOT.equiv
    exact e.injective.eq_iff
  rw [he]
  exact isClosed_eq (continuous_const_mul _) (continuous_mul_const _)

end

/-! Algebraic and isometric transport of factor structure and existential Banach preduals. -/

end Tracial

/-! First step of generation transport: compact balls and closed vector balls
for the represented intersection with any original WOT-closed subalgebra. -/
open Filter
open scoped Topology CStarAlgebra
namespace Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)

local notation "K" => TraceFreeHilbert hfactor hdiff hfinite hunit

local notation "π" => traceFreeHilbertAction hfactor hdiff hfinite hunit
local notation "Ω" => traceFreeHilbertVector hfactor hdiff hfinite hunit

local notation "N" => traceFreeHilbertClosure hfactor hdiff hfinite hunit

local instance traceSubalgebraBallOperatorCStar_r21cd40_1 : CStarAlgebra (K →L[ℂ] K) := {}
variable (Q : StarSubalgebra ℂ (H →L[ℂ] H))

attribute [local instance] OAI.Generator.Tracial.traceSubalgebraBallCStar
local instance traceSubalgebraBallOrder_r21cd40_1 : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance traceSubalgebraBallStarOrder_r21cd40_1 : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
local instance traceSubalgebraBallClosureCStar_r21cd40_1 : CStarAlgebra (N).toStarSubalgebra := {}
theorem traceFreeSubalgebraWeakBall_isCompact (hQ : WOTClosed Q) (C : ℝ) :
    IsCompact (traceFreeSubalgebraWeakBall hfactor hdiff hfinite hunit Q C) := by
  let : CompactSpace (weakOperatorBall M C) :=
    isCompact_iff_compactSpace.mp (weakOperatorBall_isCompact M C)
  have hc : IsCompact {T : weakOperatorBall M C | T.val.toCLM ∈ Q} :=
    (hQ.preimage continuous_subtype_val).isCompact
  have he : traceFreeSubalgebraWeakBall hfactor hdiff hfinite hunit Q C =
      traceFreeHilbertBallMap hfactor hdiff hfinite hunit C ''
        {T : weakOperatorBall M C | T.val.toCLM ∈ Q} := by
    ext T
    constructor
    · rintro ⟨a,ha,hn,rfl⟩
      exact ⟨⟨ContinuousLinearMapWOT.ofCLM a.val,⟨a.property,hn⟩⟩,ha,rfl⟩
    · rintro ⟨a,ha,rfl⟩
      exact ⟨⟨a.val.toCLM,a.property.1⟩,ha,a.property.2,rfl⟩
  rw [he]
  exact hc.image (traceFreeHilbertBallMap_continuous hfactor hdiff hfinite hunit C)

theorem traceFreeSubalgebraVectorBall_isClosed (hQ : WOTClosed Q) (C : ℝ) :
    IsClosed (traceFreeSubalgebraVectorBall hfactor hdiff hfinite hunit Q C) := by
  apply IsSeqClosed.isClosed
  intro v x hv hx
  choose a hQmem ha he using hv
  let ω : Ultrafilter ℕ := Ultrafilter.of atTop
  obtain ⟨T,hT,ht⟩ := (traceFreeSubalgebraWeakBall_isCompact hfactor hdiff hfinite hunit Q hQ C).ultrafilter_le_nhds
    (ω.map (fun n => ContinuousLinearMapWOT.ofCLM (π (a n)))) (by
      apply le_principal_iff.mpr
      change ∀ᶠ n in (ω : Filter ℕ), ContinuousLinearMapWOT.ofCLM (π (a n)) ∈
        traceFreeSubalgebraWeakBall hfactor hdiff hfinite hunit Q C
      exact Eventually.of_forall (fun n => ⟨a n,hQmem n,ha n,rfl⟩))
  obtain ⟨b,hbQ,hb,rfl⟩ := hT
  refine ⟨b,hbQ,hb,?_⟩
  apply ext_inner_left ℂ
  intro y
  have hw := (ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto.mp ht) Ω y
  change Tendsto (fun n => inner ℂ y (π (a n) Ω)) (ω : Filter ℕ)
    (𝓝 (inner ℂ y (π b Ω))) at hw
  have hn := (innerSL ℂ y).continuous.continuousAt.tendsto.comp
    (hx.mono_left (Ultrafilter.of_le atTop))
  exact tendsto_nhds_unique hw (by simpa only [Function.comp_def,innerSL_apply_apply,he] using hn)

theorem traceSymmetrize_mem_original (a : M.toStarSubalgebra) (ha : a.val ∈ Q) :
    (traceSymmetrize a).val ∈ Q := by
  have hs : star a.val ∈ Q := star_mem ha
  exact Q.smul_mem (Q.add_mem ha hs) _

theorem traceClip_mem_original (hQ : WOTClosed Q) (a : M.toStarSubalgebra)
    (haQ : a.val ∈ Q) (ha : IsSelfAdjoint a) (C : ℝ) : (traceClip a C).val ∈ Q := by
  let P := Q.comap M.toStarSubalgebra.subtype
  let : IsClosed (P : Set M.toStarSubalgebra) :=
    (hQ.preimage ContinuousLinearMapWOT.continuous_ofCLM).preimage continuous_subtype_val
  change traceClip a C ∈ P
  rw [traceClip_cfc a ha C]
  exact cfc_mem (𝕜' := ℂ) (fun t : ℝ => -min (-min t C) C) haQ

end Tracial

/-! Closed images of original WOT-closed subalgebras in the constructed representation. -/
open Filter
open scoped Topology CStarAlgebra ComplexStarModule
namespace Tracial

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)

local notation "K" => TraceFreeHilbert hfactor hdiff hfinite hunit

local notation "π" => traceFreeHilbertAction hfactor hdiff hfinite hunit
local notation "Ω" => traceFreeHilbertVector hfactor hdiff hfinite hunit

local notation "N" => traceFreeHilbertClosure hfactor hdiff hfinite hunit
local notation "ρ" => traceFreeHilbertIntoClosure hfactor hdiff hfinite hunit
local notation "σ" => traceFreeHilbertClosureTrace hfactor hdiff hfinite hunit

attribute [local instance] OAI.Generator.Tracial.traceSubalgebraImageOperatorCStar
variable (Q : StarSubalgebra ℂ (H →L[ℂ] H))

local notation "P" => StarSubalgebra.map π (StarSubalgebra.comap
  (StarSubalgebra.subtype (VonNeumannAlgebra.toStarSubalgebra M)) Q)

local notation "R" => traceFreeSubalgebraClosure hfactor hdiff hfinite hunit Q

local notation "j" => traceFreeSubalgebraInclusion hfactor hdiff hfinite hunit Q

attribute [local instance] OAI.Generator.Tracial.traceSubalgebraImageCStar
local instance traceSubalgebraImageOrder_r21cd40_1 : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance traceSubalgebraImageStarOrder_r21cd40_1 : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
attribute [local instance] OAI.Generator.Tracial.traceSubalgebraImageClosureCStar
theorem traceFreeSubalgebra_selfAdjoint_approximation
    (hQ : WOTClosed Q) (x : (R).toStarSubalgebra) (hx : IsSelfAdjoint x)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ a : M.toStarSubalgebra, a.val ∈ Q ∧ IsSelfAdjoint a ∧ ‖a‖ ≤ ‖j x‖ ∧
      (σ).norm₂ (ρ a-j x) < ε := by
  classical
  obtain ⟨v,hv⟩ := bicommutant_finite_strong_approximation P x.val
    ((traceFreeSubalgebraClosure_mem_iff hfactor hdiff hfinite hunit Q x.val).mp x.property)
    {Ω} ε hε
  obtain ⟨a,haQ,ha⟩ := v.property
  change π a = v.val at ha
  have ha' : (σ).norm₂ (ρ a-j x) < ε := by
    change ‖π a Ω-x.val Ω‖ < ε
    have happrox := hv Ω (Finset.mem_singleton_self Ω)
    change ‖x.val Ω-v.val Ω‖ < ε at happrox
    rw [← ha] at happrox
    simpa only [norm_sub_rev] using happrox
  let b := traceSymmetrize a
  have hb : IsSelfAdjoint b := traceSymmetrize_selfAdjoint a
  have hbQ : b.val ∈ Q := traceSymmetrize_mem_original Q a haQ
  have hJ : IsSelfAdjoint (j x) := hx.map j
  have hb' : (σ).norm₂ (ρ b-j x) ≤ (σ).norm₂ (ρ a-j x) := by
    have he : ρ b-j x = traceSymmetrize (ρ a-j x) := by
      rw [traceSymmetrize_sub,traceSymmetrize_eq_self (j x) hJ]
      exact congrArg (fun z => z-j x)
        (traceFreeHilbertIntoClosure_symmetrize hfactor hdiff hfinite hunit a)
    rw [he]
    exact traceSymmetrize_norm₂_le σ _
  refine ⟨traceClip b ‖j x‖,
    traceClip_mem_original Q hQ b hbQ hb _,
    traceClip_selfAdjoint b hb _,traceClip_norm_le b hb _ (norm_nonneg _),?_⟩
  rw [traceFreeHilbertIntoClosure_clip hfactor hdiff hfinite hunit b hb]
  exact (traceClip_distance σ (ρ b) (j x) (hb.map ρ) hJ).trans_lt (hb'.trans_lt ha')

theorem traceFreeSubalgebra_selfAdjoint_preimage
    (hQ : WOTClosed Q) (x : (R).toStarSubalgebra) (hx : IsSelfAdjoint x) :
    ∃ a : M.toStarSubalgebra, a.val ∈ Q ∧ ρ a = j x := by
  have hm : x.val Ω ∈ traceFreeSubalgebraVectorBall hfactor hdiff hfinite hunit Q ‖j x‖ := by
    apply (traceFreeSubalgebraVectorBall_isClosed hfactor hdiff hfinite hunit Q hQ ‖j x‖).closure_subset
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨a,haQ,_,ha,hax⟩ := traceFreeSubalgebra_selfAdjoint_approximation
      hfactor hdiff hfinite hunit Q hQ x hx ε hε
    exact ⟨π a Ω,⟨a,haQ,ha,rfl⟩,by
      change ‖π a Ω-x.val Ω‖ < ε at hax
      simpa only [dist_eq_norm,norm_sub_rev] using hax⟩
  obtain ⟨a,haQ,_,ha⟩ := hm
  refine ⟨a,haQ,?_⟩
  apply sub_eq_zero.mp
  apply (σ).separating
  change π a Ω-x.val Ω = 0
  exact sub_eq_zero.mpr ha

theorem traceFreeSubalgebraClosure_preimage
    (hQ : WOTClosed Q) (x : (R).toStarSubalgebra) :
    ∃ a : M.toStarSubalgebra, a.val ∈ Q ∧ ρ a = j x := by
  obtain ⟨a,haQ,ha⟩ := traceFreeSubalgebra_selfAdjoint_preimage hfactor hdiff hfinite hunit Q hQ
    (ℜ x) (ℜ x).property
  obtain ⟨b,hbQ,hb⟩ := traceFreeSubalgebra_selfAdjoint_preimage hfactor hdiff hfinite hunit Q hQ
    (ℑ x) (ℑ x).property
  refine ⟨a+Complex.I • b,Q.add_mem haQ (Q.smul_mem hbQ _),?_⟩
  rw [map_add,map_smul,ha,hb,← map_smul,← map_add]
  exact congrArg j (realPart_add_I_smul_imaginaryPart x)

theorem traceFreeSubalgebraImage_eq_closure (hQ : WOTClosed Q) :
    P = (R).toStarSubalgebra := by
  apply le_antisymm
  · intro T hT
    apply (traceFreeSubalgebraClosure_mem_iff hfactor hdiff hfinite hunit Q T).mpr
    exact fun a ha => (ha T hT).symm
  · intro T hT
    obtain ⟨a,haQ,ha⟩ := traceFreeSubalgebraClosure_preimage hfactor hdiff hfinite hunit Q hQ ⟨T,hT⟩
    exact ⟨a,haQ,congrArg Subtype.val ha⟩

/-- Every original WOT-closed subalgebra has WOT-closed represented intersection.
No cyclicity of its orbit, factor hypothesis on Q, or full WOT continuity is used. -/
theorem traceFreeSubalgebraImage_wotClosed (hQ : WOTClosed Q) :
    WOTClosed ((Q.comap M.toStarSubalgebra.subtype).map π) := by
  rw [traceFreeSubalgebraImage_eq_closure hfactor hdiff hfinite hunit Q hQ]
  exact traceHilbertVonNeumann_wotClosed R

end

/-! Generation pullback for the actual constructed trace representation. -/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)

local notation "K" => TraceFreeHilbert hfactor hdiff hfinite hunit

local notation "π" => traceFreeHilbertAction hfactor hdiff hfinite hunit

local notation "N" => traceFreeHilbertClosure hfactor hdiff hfinite hunit

local notation "e" => traceFreeHilbertEquiv hfactor hdiff hfinite hunit

attribute [local instance] OAI.Generator.Tracial.traceGenerationTransportCStar
local instance traceGenerationTransportOrder_r21cd40_1 : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance traceGenerationTransportStarOrder_r21cd40_1 : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
attribute [local instance] OAI.Generator.Tracial.traceGenerationTransportOperatorCStar
local instance traceGenerationTransportClosureCStar_r21cd40_1 : CStarAlgebra (N).toStarSubalgebra := {}
/-- Pull a literal W*-generator back through the constructed representation.
Closed images of the original generated subalgebra replace any unproved
whole-carrier weak-operator continuity assertion. -/
theorem traceFreeHilbert_singlyGenerated_pullback_oai
    (hgen : SinglyGenerated (N).toStarSubalgebra) : SinglyGenerated M.toStarSubalgebra := by
  obtain ⟨b,hb,hgen⟩ := hgen
  let a : M.toStarSubalgebra := (e).symm ⟨b,hb⟩
  let Q := wstar {a.val}
  have hQM : Q ≤ M.toStarSubalgebra :=
    wstar_le (traceHilbertVonNeumann_wotClosed M) (by
      intro c hc
      obtain rfl := Set.mem_singleton_iff.mp hc
      exact a.property)
  let P := (Q.comap M.toStarSubalgebra.subtype).map π
  have hbP : b ∈ P := by
    refine ⟨a,subset_wstar {a.val} (Set.mem_singleton a.val),?_⟩
    exact congrArg Subtype.val ((e).apply_symm_apply ⟨b,hb⟩)
  have hNP : (N).toStarSubalgebra ≤ P := by
    rw [← hgen]
    exact wstar_le (traceFreeSubalgebraImage_wotClosed hfactor hdiff hfinite hunit Q
      (wstar_closed {a.val})) (by
        intro c hc
        obtain rfl := Set.mem_singleton_iff.mp hc
        exact hbP)
  refine ⟨a.val,a.property,le_antisymm hQM ?_⟩
  intro c hc
  obtain ⟨d,hdQ,hd⟩ := hNP (traceFreeHilbertAction_mem_closure hfactor hdiff hfinite hunit ⟨c,hc⟩)
  have hd' : d = (⟨c,hc⟩ : M.toStarSubalgebra) :=
    traceFreeHilbertAction_injective hfactor hdiff hfinite hunit hd
  change d.val ∈ Q at hdQ
  rw [hd'] at hdQ
  exact hdQ

end Tracial

end Generator

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Generator.Tracial.traceFreeHilbert_singlyGenerated_pullback_oai.{u_1} := @OAI.Generator.Tracial.traceFreeHilbert_singlyGenerated_pullback_oai.{u_1}
