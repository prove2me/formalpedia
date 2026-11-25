-- Prove2me | solution 1 for GlobalTheory.HolZeros.simple_zeros_move_holomorphically
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:23:38.894811+00:00
-- url     : https://prove2.me/submissions/74e4b3c5-066e-4157-b790-443fbfe024e3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_LevBasis
import Definitions.Def_Development_AbelianVarietyTheory_Statements_ThetaLevelCharacters_MemThetaLevelCharDimZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KaRuleK
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SndFDerivAddSndFDerivIEqZeroOfHarmonicAtLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SimpleZerosMoveHolomorphically
import Theorems.Thm_GlobalTheory_HolZeros_coords_comb
import Theorems.Thm_GlobalTheory_HolZeros_comb_coords
import Theorems.Thm_GlobalTheory_HolZeros_continuousAt_coords
import Theorems.Thm_GlobalTheory_HolZeros_continuous_comb
import Theorems.Thm_GlobalTheory_HolZeros_exists_implicit
import Theorems.Thm_GlobalTheory_HolZeros_comb_add
import Theorems.Thm_GlobalTheory_HolZeros_comb_int
import Theorems.Thm_GlobalTheory_HolZeros_IsLevel_zero_iff
import Theorems.Thm_GlobalTheory_SCV_contDiffAt_of_differentiableOn
import Theorems.Thm_GlobalTheory_differentiable_phSym_coords
import Theorems.Thm_GlobalTheory_isOpen_phDom
import Theorems.Thm_GlobalTheory_thetaLevelBasis_apply
import Theorems.Thm_GlobalTheory_thetaLevelCharBasis_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.thetaLevelBasis_apply
attribute [local simp] GlobalTheory.thetaLevelCharBasis_apply



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open Filter Topology
open GlobalTheory GlobalTheory.HolZeros
namespace GlobalTheory.HolZeros
theorem _root_.solution :
    ∀ (g n d : ℕ) (a b : Fin g → ℂ) (F : Fin g → (Fin g → Fin g → ℂ) → (Fin g → ℂ) → ℂ) (p₀ : (Fin g → Fin g → ℂ)) (z₀ : Fin d → Fin g → ℂ), p₀ ∈ Key.phDom g → (∀ i, HolFam (Key.phDom g) (F i)) → (∀ i, ∀ p ∈ Key.phDom g, IsLevel (per p) a b n (F i p)) → let Good : (Fin g → Fin g → ℂ) → (Fin d → Fin g → ℂ) → Prop := fun p z => (∀ e i, F i p (z e) = 0) ∧ (∀ e, (Matrix.of fun i k => fderiv ℂ (F i p) (z e) (Pi.single k 1)).det ≠ 0) ∧ (∀ e e' (m m' : Fin g → ℤ), z e = z e' + ((fun i => (m i : ℂ)) + (per p).mulVec (fun i => (m' i : ℂ))) → e = e') ∧ ∀ y, (∀ i, F i p y = 0) → ∃ (e : Fin d) (m m' : Fin g → ℤ), y = z e + ((fun i => (m i : ℂ)) + (per p).mulVec (fun i => (m' i : ℂ))); Good p₀ z₀ → ∃ (W : Set (Fin g → Fin g → ℂ)) (z : (Fin g → Fin g → ℂ) → Fin d → Fin g → ℂ), IsOpen W ∧ p₀ ∈ W ∧ W ⊆ Key.phDom g ∧ z p₀ = z₀ ∧ DifferentiableOn ℂ z W ∧ ∀ p ∈ W, Good p (z p) := by
  intro g n d a b F p₀ z₀ hp₀ hF hL Good hG
  obtain ⟨h0, hd, hdist, hex⟩ := hG
  have hdom : Key.phDom g ∈ 𝓝 p₀ := (GlobalTheory.isOpen_phDom g).mem_nhds hp₀
  have hcd : ∀ i y, ContDiffAt ℂ 1
      (fun q : (Fin g → Fin g → ℂ) × (Fin g → ℂ) => F i q.1 q.2) (p₀, y) := fun i y =>
    GlobalTheory.SCV.contDiffAt_of_differentiableOn (hF i) (prod_mem_nhds hdom univ_mem) 1
  choose ζ hζ0 hζd hζz hζj hζu using fun e =>
    exists_implicit F p₀ (z₀ e) (fun i => hcd i _) (h0 e) (hd e)
  have hτ : Continuous fun p : Fin g → Fin g → ℂ => per p :=
    GlobalTheory.differentiable_phSym_coords.continuous
  have hun : ∀ p ∈ Key.phDom g, IsUnit ((per p).map Complex.im).det := fun p hp =>
    (Matrix.isUnit_iff_isUnit_det _).1 hp.2.isUnit

  have hS : IsClosed {x : (Fin g → ℝ) × (Fin g → ℝ) | ∀ i,
      x.1 i ∈ Set.range ((↑) : ℤ → ℝ) ∧ x.2 i ∈ Set.range ((↑) : ℤ → ℝ)} := by
    simp only [Set.setOf_forall]
    refine isClosed_iInter fun i => IsClosed.inter ?_ ?_
    · exact Int.isClosedEmbedding_coe_real.isClosed_range.preimage
        (f := fun x : (Fin g → ℝ) × (Fin g → ℝ) => x.1 i) (by fun_prop)
    · exact Int.isClosedEmbedding_coe_real.isClosed_range.preimage
        (f := fun x : (Fin g → ℝ) × (Fin g → ℝ) => x.2 i) (by fun_prop)
  have hD : ∀ e e', ∀ᶠ p in 𝓝 p₀, ∀ m m' : Fin g → ℤ, ζ e p = ζ e' p +
      ((fun i => (m i : ℂ)) + (per p).mulVec (fun i => (m' i : ℂ))) → e = e' := by
    intro e e'
    by_cases hee : e = e'
    · exact Eventually.of_forall fun _ _ _ _ => hee
    have hc := continuousAt_coords (w := fun p => ζ e p - ζ e' p) hτ
      ((hζd e).self_of_nhds.continuousAt.sub (hζd e').self_of_nhds.continuousAt) (hun p₀ hp₀)
    have hn : coords (per p₀) (ζ e p₀ - ζ e' p₀) ∈ {x : (Fin g → ℝ) × (Fin g → ℝ) | ∀ i,
        x.1 i ∈ Set.range ((↑) : ℤ → ℝ) ∧ x.2 i ∈ Set.range ((↑) : ℤ → ℝ)}ᶜ := by
      intro h
      choose m hm using fun i => (h i).1
      choose m' hm' using fun i => (h i).2
      refine hee (hdist e e' m m' ?_)
      have h1 : coords (per p₀) (ζ e p₀ - ζ e' p₀) = (fun i => (m i : ℝ), fun i => (m' i : ℝ)) :=
        Prod.ext (funext fun i => (hm i).symm) (funext fun i => (hm' i).symm)
      rw [← comb_int, ← h1, comb_coords (hun p₀ hp₀), hζ0, hζ0, add_sub_cancel]
    filter_upwards [hc.eventually (hS.isOpen_compl.mem_nhds hn), hdom] with p hp hpd m m' h
    refine absurd ?_ hp
    rw [h, add_sub_cancel_left, ← comb_int, coords_comb (hun p hpd)]
    exact fun i => ⟨⟨m i, rfl⟩, ⟨m' i, rfl⟩⟩

  have hK : IsCompact (Set.Icc (0 : (Fin g → ℝ) × (Fin g → ℝ)) 1) := isCompact_Icc
  have hcc : Continuous fun q : (Fin g → Fin g → ℂ) × ((Fin g → ℝ) × (Fin g → ℝ)) =>
      comb (per q.1) q.2 := continuous_comb (hτ.comp continuous_fst) continuous_snd
  have hE : ∀ᶠ p in 𝓝 p₀, ∀ x ∈ Set.Icc (0 : (Fin g → ℝ) × (Fin g → ℝ)) 1,
      (∀ i, F i p (comb (per p) x) = 0) → ∃ (e : Fin d) (m m' : Fin g → ℤ), comb (per p) x =
        ζ e p + ((fun i => (m i : ℂ)) + (per p).mulVec (fun i => (m' i : ℂ))) := by
    refine hK.eventually_forall_of_forall_eventually fun x₀ _ => ?_
    by_cases hz : ∀ i, F i p₀ (comb (per p₀) x₀) = 0
    · obtain ⟨e, m, m', he⟩ := hex _ hz
      have hc2 : Continuous fun q : (Fin g → Fin g → ℂ) × ((Fin g → ℝ) × (Fin g → ℝ)) =>
          (q.1, comb (per q.1) q.2 -
            comb (per q.1) (fun i => (m i : ℝ), fun i => (m' i : ℝ))) :=
        continuous_fst.prodMk (hcc.sub (continuous_comb (hτ.comp continuous_fst) continuous_const))
      have ht := hc2.tendsto (p₀, x₀)
      simp only [comb_int, he, add_sub_cancel_right] at ht
      filter_upwards [ht.eventually (hζu e), continuousAt_fst.eventually
        (show ∀ᶠ p in 𝓝 (p₀, x₀).1, p ∈ Key.phDom g from hdom)] with q hq hqd hq0
      refine ⟨e, m, m', ?_⟩
      rw [hq fun i => ?_, sub_add_cancel]
      rw [← IsLevel.zero_iff (hL i q.1 hqd) m m', sub_add_cancel]
      exact hq0 i
    · push Not at hz
      obtain ⟨i, hi⟩ := hz
      have hc : ContinuousAt (fun q : (Fin g → Fin g → ℂ) × ((Fin g → ℝ) × (Fin g → ℝ)) =>
          F i q.1 (comb (per q.1) q.2)) (p₀, x₀) :=
        ContinuousAt.comp (f := fun q : (Fin g → Fin g → ℂ) × ((Fin g → ℝ) × (Fin g → ℝ)) =>
          (q.1, comb (per q.1) q.2)) (x := (p₀, x₀)) (hcd i (comb (per p₀) x₀)).continuousAt
          (continuous_fst.prodMk hcc).continuousAt
      filter_upwards [hc.eventually_ne hi] with q hq h
      exact absurd (h i) hq
  have hall : ∀ᶠ p in 𝓝 p₀, p ∈ Key.phDom g ∧ DifferentiableAt ℂ (fun p e => ζ e p) p ∧
      Good p (fun e => ζ e p) := by
    filter_upwards [hdom, eventually_all.2 hζd, eventually_all.2 hζz, eventually_all.2 hζj,
      eventually_all.2 fun e => eventually_all.2 (hD e), hE] with p hp h1 h2 h3 h4 h5
    refine ⟨hp, differentiableAt_pi.2 h1, h2, h3, h4, fun y hy => ?_⟩
    set c := coords (per p) y with hc
    let x : (Fin g → ℝ) × (Fin g → ℝ) := (fun i => Int.fract (c.1 i), fun i => Int.fract (c.2 i))
    have hy' : y = comb (per p) x + ((fun i => ((⌊c.1 i⌋ : ℤ) : ℂ)) +
        (per p).mulVec (fun i => ((⌊c.2 i⌋ : ℤ) : ℂ))) := by
      rw [← comb_int, ← comb_add, ← comb_coords (hun p hp) y, ← hc]
      congr 1
      ext i <;> simp [x]
    obtain ⟨e, m, m', he⟩ := h5 x
      ⟨⟨fun i => Int.fract_nonneg _, fun i => Int.fract_nonneg _⟩,
        ⟨fun i => (Int.fract_lt_one _).le, fun i => (Int.fract_lt_one _).le⟩⟩ fun i => by
      rw [← IsLevel.zero_iff (hL i p hp) (fun i => ⌊c.1 i⌋) (fun i => ⌊c.2 i⌋), ← hy']
      exact hy i
    refine ⟨e, fun i => m i + ⌊c.1 i⌋, fun i => m' i + ⌊c.2 i⌋, ?_⟩
    rw [hy', he, add_assoc, ← comb_int, ← comb_int, ← comb_int, ← comb_add]
    congr 2
    ext i <;> simp
  obtain ⟨W, hW, hWo, hW0⟩ := eventually_nhds_iff.1 hall
  exact ⟨W, fun p e => ζ e p, hWo, hW0, fun p hp => (hW p hp).1, funext hζ0,
    fun p hp => (hW p hp).2.1.differentiableWithinAt, fun p hp => (hW p hp).2.2⟩
end GlobalTheory.HolZeros
