-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.preparedUniformDegreeDirectSource_of_geometry_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T07:32:18.409158+00:00
-- url     : https://prove2.me/submissions/933e9bb5-bcbe-48eb-85a0-d1b4f3556e35

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B285
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_preparedModularGeneralDirectDetectionAmbient_sharedWidth_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CanonicalDetectedScaleInputBudget
namespace OAI

section

namespace Erdos3

theorem slicedDetectionGain_lower (s C count : ℕ) {p q a α : ℝ}
    (hα : Real.exp (-a) ≤ α) :
    Real.exp (-slicedDetectionGainLog s C count p q a) ≤
      (Real.exp (-((5 * p + 20) * count + p + 2)) * (α / 2)) *
        Real.exp (-((q + C) ^ C)) ^ (2 ^ (s + 1)) := by
  have hhalf : Real.exp (-(a + 1)) ≤ α / 2 := by
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have hh : 2 * Real.exp (-(a + 1)) ≤ Real.exp (-a) := by
      calc
        _ ≤ Real.exp 1 * Real.exp (-(a + 1)) := mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
    linarith
  calc
    _ = (Real.exp (-((5 * p + 20) * count + p + 2)) * Real.exp (-(a + 1))) *
          Real.exp (-((q + C) ^ C)) ^ (2 ^ (s + 1)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1
      unfold slicedDetectionGainLog
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hhalf (Real.exp_nonneg _)) (by positivity)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalJetCoverCancellation
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical NNReal

theorem coefficientLatticeBasis_card_le {m : ℕ} {J Q : Fin m → Type*}
    [∀ j, Fintype (J j)] [∀ j, Fintype (Q j)] {n : Fin m → ℕ}
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (j : Fin m) : Fintype.card (Q j) ≤ Fintype.card (J j) := by
  have h := standardLatticeCoordinates_card (euclideanSubspace (U j)) (bW j) (b j) (hb j)
  rw [Fintype.card_sum, Fintype.card_fin] at h
  omega

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedProfileDimensions
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

include U b o

theorem allocatedProfile_dimensions
    {G : Type*} [Fintype G] (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {α : Type*} [Fintype α] {O : Fin m → Type*} [∀ j, Fintype (O j)]
    {D : ℝ} (hd : AllocatedComparisonDimensions (G := G) B α O D)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))) :
    (∀ j, (Fintype.card (J j) : ℝ) ≤ D) ∧ (∀ j, (Fintype.card (Q j) : ℝ) ≤ D) := by
  have hJ (j) : (Fintype.card (J j) : ℝ) ≤ D :=
    (Nat.cast_le.mpr (allocatedAmbientDimension_le_axes U b o j)).trans hd.axes
  exact ⟨hJ, fun j => (Nat.cast_le.mpr (coefficientLatticeBasis_card_le U b hb bW j)).trans (hJ j)⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineAmbientPrimitiveBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped NNReal

theorem affineAmbientMassLog_nonneg {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ affineAmbientMassLog P := by unfold affineAmbientMassLog; positivity

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedModularGeneralDetectorNativeBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

theorem generalDetectorCoefficientCost_single (m dim : ℕ) (j : Fin m) :
    Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1)) ≤
      generalDetectorCoefficientCost m dim := by
  exact Finset.single_le_sum (f := fun j : Fin m =>
    Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1)))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)

theorem preparedModularGeneralDetectorResources_primitive_domination
    (K : PreparedModularCanonicalDetectorResourceConstants) (dim : ℕ)
    {P L : ℝ} (hP : 0 ≤ P) (hPL : P ≤ L) :
    let r := preparedModularGeneralDetectorResources K dim P L
    P ≤ r.v ∧ P ≤ r.Dg ∧ P ≤ r.Pnative ∧
    (generalDetectorCoefficientCost K.m dim : ℝ) ≤ r.Psample ∧
    r.Pmass ≤ r.Psample ∧ r.ambient ≤ r.Psample ∧ r.Pproj ≤ r.Psample ∧
    r.Psample ≤ r.Pside ∧ L ≤ r.Pside ∧
    ∀ j : Fin K.m, (Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1)) : ℝ) ≤
      Real.exp r.Psample := by
  intro r
  have hL := hP.trans hPL
  have h := ((Classical.choose_spec
    (exists_preparedModularGeneralDetector_resource_budget K dim)).2 hP hPL).1
  have hv : P ≤ r.v := by change P ≤ P + 8; linarith
  have hD : P ≤ r.Dg := by
    have hrest : 0 ≤ (K.m : ℝ) * P + (layerTailDegree K.m + 1 : ℕ) +
        K.m + comparisonProfileBound + 8 := by positivity
    change P ≤ 2 * P + K.m * P + (layerTailDegree K.m + 1 : ℕ) + K.m + comparisonProfileBound + 8
    linarith only [hP, hrest]
  have hN : P ≤ r.Pnative := by
    change P ≤ r.Dg + r.gridlog + r.v + r.Fpref + 6 * P + r.Banalytic
    linarith only [hv, h.Dg.1, h.gridlog.1, h.Fpref.1, h.Banalytic.1, hP]
  have hpow : 0 ≤ (P + (K.m + dim + 2 : ℕ)) ^ (K.m + dim + 2) := by positivity
  have hcost0 : (0 : ℝ) ≤ generalDetectorCoefficientCost K.m dim := Nat.cast_nonneg _
  have hsample : r.Psample = r.Pmass + r.ambient + r.Pproj + 2 * P +
      generalDetectorCoefficientCost K.m dim + (P + (K.m + dim + 2 : ℕ)) ^ (K.m + dim + 2) + 8 := rfl
  have hcost : (generalDetectorCoefficientCost K.m dim : ℝ) ≤ r.Psample := by
    linarith only [hsample, h.Pmass.1, h.ambient.1, h.Pproj.1, hP, hpow]
  have hside : r.Pside = r.Psample + r.Pproj + r.Pmass + 2 * L := rfl
  refine ⟨hv, hD, hN, hcost, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith only [hsample, h.ambient.1, h.Pproj.1, hP, hcost0, hpow]
  · linarith only [hsample, h.Pmass.1, h.Pproj.1, hP, hcost0, hpow]
  · linarith only [hsample, h.Pmass.1, h.ambient.1, hP, hcost0, hpow]
  · linarith only [hside, h.Pproj.1, h.Pmass.1, hL]
  · linarith only [hside, h.Psample.1, h.Pproj.1, h.Pmass.1, hL]
  · intro j
    exact (Nat.cast_le.mpr (generalDetectorCoefficientCost_single K.m dim j)).trans
      (hcost.trans (by linarith only [Real.add_one_le_exp r.Psample]))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

private theorem generalResource_nonneg
    (K : PreparedModularCanonicalDetectorResourceConstants) (dim : ℕ)
    {P L : ℝ} (hP : 0 ≤ P) (hPL : P ≤ L) :
    ∃ budget : ℝ, (preparedModularGeneralDetectorResources K dim P L).Bounds budget := by
  obtain ⟨C, _, hbound⟩ := exists_preparedModularGeneralDetector_resource_budget K dim
  exact ⟨(P + L + C) ^ C, (hbound hP hPL).1⟩

private theorem prepared_slicedGridGeometryLog_mono_p1
    {D v w t D' v' w' t' : ℝ} (hD : 0 ≤ D) (hv : 0 ≤ v) (hw : 0 ≤ w) (ht : 0 ≤ t)
    (hDD : D ≤ D') (hvv : v ≤ v') (hww : w ≤ w') (htt : t ≤ t') :
    slicedGridGeometryLog D v w t ≤ slicedGridGeometryLog D' v' w' t' := by
  have hD' : 0 ≤ D' := hD.trans hDD
  unfold slicedGridGeometryLog
  gcongr

private theorem prepared_affineAmbientPrimitiveBudget_mono_p1
    {base Q base' Q' : ℝ} (hb : 0 ≤ base) (hQ : 0 ≤ Q)
    (hbb : base ≤ base') (hQQ : Q ≤ Q') :
    affineAmbientPrimitiveBudget base Q ≤ affineAmbientPrimitiveBudget base' Q' := by
  have hb' : 0 ≤ base' := hb.trans hbb
  have hQ' : 0 ≤ Q' := hQ.trans hQQ
  dsimp only [affineAmbientPrimitiveBudget, affineAmbientMassLog]
  gcongr

theorem preparedModularGeneralDetector_ideal_site_bound
    (K : PreparedModularCanonicalDetectorResourceConstants) (dim : ℕ) {P L : ℝ} (hP : 0 ≤ P)
    {outputs : ℕ} (hout : (outputs : ℝ) ≤ P) {sumlog : ℝ}
    (hsum : sumlog ∈ Set.Icc 0 (preparedModularGeneralDetectorResources K dim P L).sumlog) :
    idealSiteLogBudget outputs dim sumlog ∈
      Set.Icc 0 (preparedModularGeneralDetectorResources K dim P L).idealQ := by
  let r := preparedModularGeneralDetectorResources K dim P L
  have hprofile : (probabilityProfileLipschitz : ℝ) ≤ comparisonProfileBound :=
    (Nat.le_ceil _).trans (by unfold comparisonProfileBound; push_cast; linarith)
  refine ⟨(idealSiteLogBudget_bounds outputs dim hsum.1).1, ?_⟩
  change idealSiteLogBudget outputs dim sumlog ≤
    (dim : ℝ) + P * r.sumlog + (P + comparisonProfileBound + (P + 1) * r.sumlog) + r.sumlog + 1
  unfold idealSiteLogBudget affineProfileLogBound
  have hs0 := hsum.1
  have hs1 := hsum.2
  gcongr

theorem preparedModularGeneralDetector_ambient_bound
    (K : PreparedModularCanonicalDetectorResourceConstants) (dim : ℕ) {P L : ℝ} (hP : 0 ≤ P)
    {outputs : ℕ} (hout : (outputs : ℝ) ≤ P)
    {box Prho volume normalizer mask target base : ℝ}
    (hbox : box ∈ Set.Icc 0 (preparedModularGeneralDetectorResources K dim P L).Pbox)
    (hPrho : Prho ∈ Set.Icc 0 P)
    (hvolume : volume ∈ Set.Icc 0 (preparedModularGeneralDetectorResources K dim P L).Vlog)
    (hnormalizer : normalizer ∈ Set.Icc 0 (preparedModularGeneralDetectorResources K dim P L).Nlog)
    (hmask : mask ∈ Set.Icc 0 (preparedModularGeneralDetectorResources K dim P L).Q)
    (htarget : target ∈ Set.Icc 0 P)
    (hbase : base ∈ Set.Icc 0 (preparedModularGeneralDetectorResources K dim P L).baseAmbient) :
    let site := idealSiteLogBudget outputs dim (box + Prho + volume + normalizer + mask + target)
    site ∈ Set.Icc 0 (preparedModularGeneralDetectorResources K dim P L).idealQ ∧
    affineAmbientPrimitiveBudget base site ∈
      Set.Icc 0 (preparedModularGeneralDetectorResources K dim P L).ambient := by
  intro site
  have hsum : box + Prho + volume + normalizer + mask + target ∈
      Set.Icc 0 (preparedModularGeneralDetectorResources K dim P L).sumlog := by
    constructor
    · linarith only [hbox.1, hPrho.1, hvolume.1, hnormalizer.1, hmask.1, htarget.1]
    · exact add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hbox.2 hPrho.2)
        hvolume.2) hnormalizer.2) hmask.2) htarget.2
  have hsite := preparedModularGeneralDetector_ideal_site_bound K dim hP hout hsum
  refine ⟨hsite, ⟨?_, ?_⟩⟩
  · have hb := hbase.1
    have hq := hsite.1
    dsimp only [affineAmbientPrimitiveBudget, affineAmbientMassLog]
    positivity
  · exact prepared_affineAmbientPrimitiveBudget_mono_p1 hbase.1 hsite.1 hbase.2 hsite.2

theorem preparedModularGeneralDetector_grid_resource_width_bound
    (K : PreparedModularCanonicalDetectorResourceConstants) (dim : ℕ) {P L pDetect qlog : ℝ}
    (hP : 0 ≤ P) (hPL : P ≤ L) (hp : pDetect ∈ Set.Icc 0 P)
    (hq : qlog ∈ Set.Icc 0 (preparedModularGeneralDetectorResources K dim P L).Q) :
    let r := preparedModularGeneralDetectorResources K dim P L
    let tg := (dim : ℝ) + qlog + (pDetect + 1) + 1
    let pg := (K.Cgrid : ℝ) + ((dim + 1 : ℕ) : ℝ) * qlog + (pDetect + 1) + 4
    slicedGridGeometryLog r.Dg r.v r.w tg + pg ∈ Set.Icc 0 r.gridlog := by
  intro r tg pg
  obtain ⟨_, h⟩ := generalResource_nonneg K dim hP hPL
  have ht : tg ∈ Set.Icc 0 r.tq := by
    change 0 ≤ (dim : ℝ) + qlog + (pDetect + 1) + 1 ∧
      (dim : ℝ) + qlog + (pDetect + 1) + 1 ≤ (dim : ℝ) + r.Q + (P + 1) + 1
    constructor <;> linarith only [hq.1, hq.2, hp.1, hp.2, Nat.cast_nonneg (α := ℝ) dim]
  have hg : pg ∈ Set.Icc 0 r.pq := by
    change 0 ≤ (K.Cgrid : ℝ) + ((dim + 1 : ℕ) : ℝ) * qlog + (pDetect + 1) + 4 ∧
      (K.Cgrid : ℝ) + ((dim + 1 : ℕ) : ℝ) * qlog + (pDetect + 1) + 4 ≤ K.Cgrid + ((dim + 1 : ℕ) : ℝ) * r.Q + (P + 1) + 4
    have hq0 := mul_nonneg (Nat.cast_nonneg (α := ℝ) (dim + 1)) hq.1
    have hq1 := mul_le_mul_of_nonneg_left hq.2 (Nat.cast_nonneg (α := ℝ) (dim + 1))
    constructor <;> linarith only [hq0, hq1, hp.1, hp.2, Nat.cast_nonneg (α := ℝ) K.Cgrid]
  have hw : 0 ≤ r.w := h.w.1
  constructor
  · have hD := h.Dg.1
    have hv := h.v.1
    have ht0 := ht.1
    have hg0 := hg.1
    unfold slicedGridGeometryLog
    positivity
  · exact add_le_add
      (prepared_slicedGridGeometryLog_mono_p1 h.Dg.1 h.v.1 hw ht.1 le_rfl le_rfl le_rfl ht.2) hg.2

theorem preparedModularGeneralDetector_native_inputs
    (K : PreparedModularCanonicalDetectorResourceConstants) (dim : ℕ) {P L : ℝ} (hP : 0 ≤ P) (hPL : P ≤ L) :
    let r := preparedModularGeneralDetectorResources K dim P L
    r.Dg ∈ Set.Icc 0 r.Pnative ∧ r.gridlog ∈ Set.Icc 0 r.Pnative ∧
    r.v ∈ Set.Icc 0 r.Pnative ∧ r.Fpref ∈ Set.Icc 0 r.Pnative ∧
    r.Banalytic ∈ Set.Icc 0 r.Pnative ∧ P ≤ r.Pnative ∧
    ∀ a ∈ Set.Icc (0 : ℝ) P, a ∈ Set.Icc 0 r.Pnative := by
  intro r
  obtain ⟨_, h⟩ := generalResource_nonneg K dim hP hPL
  have hD := h.Dg.1
  have hg := h.gridlog.1
  have hv := h.v.1
  have hf := h.Fpref.1
  have hb := h.Banalytic.1
  have heq : r.Pnative = r.Dg + r.gridlog + r.v + r.Fpref + 6 * P + r.Banalytic := rfl
  have hpv : P ≤ r.v := by change P ≤ P + 8; linarith
  have hPnative : P ≤ r.Pnative := by linarith only [heq, hpv, hD, hg, hf, hb, hP]
  refine ⟨⟨hD, ?_⟩, ⟨hg, ?_⟩, ⟨hv, ?_⟩, ⟨hf, ?_⟩, ⟨hb, ?_⟩, hPnative, ?_⟩
  all_goals first | linarith only [heq, hD, hg, hv, hf, hb, hP] |
    exact fun a ha => ⟨ha.1, ha.2.trans hPnative⟩

theorem preparedModularGeneralDetector_required_bounds
    (K : PreparedModularCanonicalDetectorResourceConstants) (dim : ℕ) {P L : ℝ} (hP : 0 ≤ P) (hPL : P ≤ L) :
    let r := preparedModularGeneralDetectorResources K dim P L
    (r.Psample + K.Apert) ^ K.Apert ≤ r.required ∧
    (r.Pmass + K.AmassWindow) ^ K.AmassWindow ≤ r.required ∧
    (r.Pproj + K.Aproj) ^ K.Aproj ≤ r.required ∧
    (r.Pside + K.Aside) ^ K.Aside ≤ r.required ∧
    (r.full + r.E + K.Amarginal) ^ K.Amarginal ≤ r.required := by
  intro r
  obtain ⟨_, h⟩ := generalResource_nonneg K dim hP hPL
  have hs := h.Psample.1
  have hm := h.Pmass.1
  have hp := h.Pproj.1
  have hside := h.Pside.1
  have hf := h.full.1
  have he := h.E.1
  have h1 : 0 ≤ (r.Psample + K.Apert) ^ K.Apert := by positivity
  have h2 : 0 ≤ (r.Pmass + K.AmassWindow) ^ K.AmassWindow := by positivity
  have h3 : 0 ≤ (r.Pproj + K.Aproj) ^ K.Aproj := by positivity
  have h4 : 0 ≤ (r.Pside + K.Aside) ^ K.Aside := by positivity
  have h5 : 0 ≤ (r.full + r.E + K.Amarginal) ^ K.Amarginal := by positivity
  have hsum : r.required = (r.Psample + K.Apert) ^ K.Apert +
      (r.Pmass + K.AmassWindow) ^ K.AmassWindow + (r.Pproj + K.Aproj) ^ K.Aproj +
      (r.Pside + K.Aside) ^ K.Aside + (r.full + r.E + K.Amarginal) ^ K.Amarginal := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith only [hsum, h1, h2, h3, h4, h5]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PreparedModularCanonicalDetectorGeometricBoundsGeneral
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical NNReal

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (rowSets : Fin m → Finset (Finset (Fin dim)))

variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

theorem preparedModularGeneralDetector_ambient_count {P : ℝ}
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P) :
    ((∑ j, Fintype.card (J j) : ℕ) : ℝ) ≤ (m : ℝ) * P := by
  rw [Nat.cast_sum]
  calc
    _ ≤ ∑ _j : Fin m, P := Finset.sum_le_sum (fun j _ => hJ j)
    _ = _ := by simp

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedFullBoxPositiveLaw
namespace OAI

section

namespace Erdos3.VectorPolynomial
universe uX uG uI uB uJ
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

theorem allocated_fullBox_positive_law_at_model_budget (m : ℕ) :
    let A := Classical.choose (exists_allocated_fullBox_normalized_approximation.{uX,uG,uI,uB,uJ,0} m)
    ∀ {X : Type uX} {G : Type uG} [Fintype X] [DecidableEq X] [Fintype G] [DecidableEq G]
    {I : Fin m → Type uI} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
    {J : Fin m → Type uJ} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
    (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (_hσ1 : ∀ j, σ j ≤ 1)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ V j)
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    {P E : ℝ} (_hP : 0 ≤ P) (_hmSize : (m : ℝ) ≤ P)
    (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ P)
    (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (_hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) (_hLP : (S.value : ℝ) ≤ Real.exp P)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : X → ℕ) (_hs : ∀ d, 0 < stride d) (_hsP : ∀ d, (stride d : ℝ) ≤ Real.exp P)
    {W τ ξ : ℝ} (_hW : 0 ≤ W) (_hWP : W ≤ Real.exp P)
    (_hRootBudget : allocatedPhysicalRootBudget B U basis S (fun _ => 0) ≤ W)
    (_hτ : 0 < τ) (_hτP : τ⁻¹ ≤ Real.exp P)
    (_hτhalf : τ ≤ 1 / 2) (_hτdim : (Fintype.card X : ℝ) * τ ≤ 1 / 2)
    (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hξP : ξ⁻¹ ≤ Real.exp P)
    (N : X → ℕ) (_hsize : ∀ d, Real.exp ((max P E + A) ^ A) ≤ (N d : ℝ))
    {rank : ℝ} (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (p j))
    (_hRank : Real.exp ((max P E + A) ^ A) ≤ rank)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty),
    let widths := narrowTrimmedSpatialWidths (G := G)
      (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let bases := trimmedIntegerBox N (spatialTrimMargin τ N)
    let density := allocatedJointBaseDensity B U basis hb o hR hσ S X p hm
    let Z := selectedJointDensityMass bases stride T widths density
    ∃ (_hN : ∀ x, 0 < N x) (_hbases : bases.Nonempty) (_hbox : (integerBox N).Nonempty)
      (_hmass : 0 < ∑' z, selectedResidueSmoothWeight stride T widths z),
    ∃ _hnormalizer : |Z - 1| ≤ Real.exp (-E) ∧
      Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧ 0 < Z ∧ Z⁻¹ ≤ 2,
    ∀ x, 2 * spatialTrimMargin τ N x ≤ N x := by
  intro A X G _ _ _ _ I _ _ n B _ _ J _ U basis R σ S hb o _ _ _ _ μ _ _ ν _ _
    hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall P E hP hmSize hK hX hdim
    hRP hσP hcount hI hn hJ hAP hLP hCP hVP p hp hm stride hs hsP W τ ξ
    hW hWP hRootBudget hτ hτP hτhalf hτdim hξ hξ1 hξP N hsize rank hrank hRank T hT
    widths bases density Z
  obtain ⟨hN, hbases, hbox, hmass, hnormalizer, hmargin, _⟩ :=
    (Classical.choose_spec
      (exists_allocated_fullBox_normalized_approximation.{uX,uG,uI,uB,uJ,0} m)).2
      B U basis S hb o μ ν hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall
      hP hmSize hK hX hdim hRP hσP hcount hI hn hJ hAP hLP hCP hVP p hp hm stride hs hsP
      hW hWP hRootBudget hτ hτP hτhalf hτdim hξ hξ1 hξP N hsize hrank hRank T hT
  exact ⟨hN, hbases, hbox, hmass, hnormalizer, hmargin⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PreparedModularCanonicalDetectorSpatialBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ b, Fintype (B b)]

theorem preparedModularDetector_physical_root_of_variables
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
    {P : ℝ} (_hP : 0 ≤ P)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (hS : (S.value : ℝ) ≤ Real.exp P) :
    allocatedPhysicalRootBudget B U basis S (fun _ => 0) ≤ Real.exp (2 * P + 8) := by
  have hvarsExp : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Real.exp P :=
    hvars.trans (by linarith [Real.add_one_le_exp P])
  rw [allocatedPhysicalRootBudget_zero]
  calc
    _ ≤ Real.exp P * Real.exp P :=
      mul_le_mul hvarsExp hS (Nat.cast_nonneg _) (Real.exp_nonneg _)
    _ = Real.exp (2 * P) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedModularCanonicalDetectorPositive
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

theorem preparedModularCanonicalDetector_narrow_width_le_one
    (X T : Type*) [Fintype X] [Fintype T] {G : Type*} [Fintype G]
    {q : ℕ} (selection : Fin q ↪ G) (Mk : ℕ) (p E : ℝ) :
    normalizedTupleNarrowWidth X T selection Mk p E ≤ 1 := by
  exact min_le_left _ _

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedModularGeneralDetectorThreshold
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem allocatedDetectedGain_lower (s count : ℕ) (Pdetect : Polynomial ℕ)
    {p q a α pGain : ℝ} (hα : Real.exp (-a) ≤ α)
    (hlog : slicedDetectionGainLog s (sampledSupportedSlicedDetectionConstant s Pdetect)
      count p q a ≤ pGain) :
    Real.exp (-pGain) / 2 ≤ allocatedDetectedGain s count Pdetect p q α / 2 := by
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact (Real.exp_le_exp.mpr (neg_le_neg hlog)).trans
    (slicedDetectionGain_lower s (sampledSupportedSlicedDetectionConstant s Pdetect) count hα)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedModularGeneralDetectorSamplingBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal

theorem boundedCoefficientExponent_card_mono_embedding {A T : Type*}
    [Fintype A] [Fintype T] (e : A ↪ T) (h : ℕ) :
    Fintype.card (BoundedCoefficientExponent A h) ≤
      Fintype.card (BoundedCoefficientExponent T h) := by
  let f : BoundedCoefficientExponent A h → BoundedCoefficientExponent T h := fun d =>
    ⟨Finsupp.embDomain e d.val, by
      simpa only [Finsupp.embDomain_eq_mapDomain, Finsupp.degree_mapDomain] using d.property⟩
  apply Fintype.card_le_of_injective f
  intro a b hab
  exact Subtype.ext ((Finsupp.embDomain_injective e) (congrArg Subtype.val hab))

theorem coefficientAmbientIndex_card_from_layer_counts {K : Type*} [Fintype K]
    {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)] {P : ℝ}
    (hP : 0 ≤ P)
    (hc : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent K (j.val + 1)) : ℝ) ≤ P)
    (hJ : (∑ j : Fin m, (Fintype.card (J j) : ℝ)) ≤ m * P) :
    (Fintype.card (CoefficientAmbientIndex K J) : ℝ) ≤ m * P ^ 2 ∧
      (∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent K (j.val + 1)) : ℝ)) ≤ m * P ∧
      ((∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent K (j.val + 1)) : ℝ≥0) : ℝ≥0) : ℝ) ≤ m * P := by
  have hsum : (∑ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent K (j.val + 1)) : ℝ)) ≤ m * P := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
      Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) => hc j)
  refine ⟨?_, hsum, ?_⟩
  · calc
      _ = ∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent K (j.val + 1)) : ℝ) *
          Fintype.card (J j) := by
        simp only [CoefficientAmbientIndex, CoefficientSlot, Fintype.card_sigma,
          Nat.cast_sum, Fintype.sum_sigma]
        apply Finset.sum_congr rfl
        intro j _
        change (∑ _d : BoundedCoefficientExponent K (j.val + 1), (Fintype.card (J j) : ℝ)) = _
        simp
      _ ≤ ∑ j : Fin m, P * (Fintype.card (J j) : ℝ) :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hc j) (Nat.cast_nonneg _))
      _ = P * ∑ j : Fin m, (Fintype.card (J j) : ℝ) := (Finset.mul_sum _ _ _).symm
      _ ≤ P * (m * P) := mul_le_mul_of_nonneg_left hJ hP
      _ = m * P ^ 2 := by ring
  · simpa only [NNReal.coe_sum, NNReal.coe_natCast] using hsum

theorem preparedModularGeneralDetector_jet_counts_of_geometry
    {m dim : ℕ} {G : Type*} [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {O : Fin m → Type*} [∀ j, Fintype (O j)] {D P : ℝ}
    (selection : Fin dim ↪ G)
    (hdim : AllocatedComparisonDimensions (G := G) B (Fin dim) O D) (hDP : D ≤ P) :
    ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1)) : ℝ) ≤ P := by
  let e : Fin dim ↪ LayerSamplerVariables G I n B :=
    selection.trans Function.Embedding.inl
  intro j
  exact (Nat.cast_le.mpr (boundedCoefficientExponent_card_mono_embedding e (j.val + 1))).trans
    ((hdim.coefficients j).trans hDP)

variable {m dim nX : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable {T : Type*} [Fintype T] (stride : Fin nX → ℕ)

theorem preparedModularGeneralDetector_sampling_bounds
    (K : PreparedModularCanonicalDetectorResourceConstants) (_hm : K.m = m)
    {P L target Pphysical Qstride Pk : ℝ} (hP : 0 ≤ P) (hPL : P ≤ L)
    (hAsample : 2 ≤ K.Asample)
    (hmP : (m : ℝ) ≤ P) (hdimP : (dim : ℝ) ≤ P)
    (hX : (nX : ℝ) ≤ P) (hT : (Fintype.card T : ℝ) ≤ 2 * P)
    (hJ : ((∑ j, Fintype.card (J j) : ℕ) : ℝ) ≤ (m : ℝ) * P)
    (hcoeff : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1)) : ℝ) ≤ P)
    (htarget : target ≤ P) (hphysical : Pphysical ≤ P)
    (hQstride : Qstride ≤ P) (hPk : Pk ≤ P)
    (hstride : ∀ i, (stride i : ℝ) ≤ Real.exp Qstride)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ P) :
    PreparedModularGeneralDetectorSamplingBounds (dim := dim) (J := J) (T := T) stride
      (preparedModularGeneralDetectorResources K dim P L) P L target Pphysical Qstride Pk := by
  let r := preparedModularGeneralDetectorResources K dim P L
  have hL := hP.trans hPL
  have bounds := ((Classical.choose_spec
    (exists_preparedModularGeneralDetector_resource_budget K dim)).2 hP hPL).1
  obtain ⟨_, _, _, _, hmassSample, hAmbientSample, hprojSample, hsampleSide, hLSide, _⟩ :=
    preparedModularGeneralDetectorResources_primitive_domination K dim hP hPL
  have hprojEq : r.Pproj = 4 * (L + 8)^2 := rfl
  have hproj1 : 1 ≤ r.Pproj := by nlinarith only [hprojEq, hL, sq_nonneg L]
  have hLproj : L ≤ r.Pproj := by nlinarith only [hprojEq, hL, sq_nonneg L]
  have hPproj : P ≤ r.Pproj := hPL.trans hLproj
  have h2Pproj : 2 * P ≤ r.Pproj := by
    nlinarith only [hprojEq, hL, hPL, sq_nonneg L]
  have hGainProj : P + 32 ≤ r.Pproj := by
    nlinarith only [hprojEq, hL, hPL, sq_nonneg L]
  have hframeProj : (2 * P + 1) * P ≤ r.Pproj := by
    have hsq : P^2 ≤ L^2 := pow_le_pow_left₀ hP hPL 2
    nlinarith only [hprojEq, hP, hPL, hsq, sq_nonneg L]
  have hprojSqMass : r.Pproj^2 ≤ r.Pmass := by
    change r.Pproj^2 ≤ (r.Pproj + K.Asample)^K.Asample
    have hAs : (0 : ℝ) ≤ K.Asample := Nat.cast_nonneg _
    exact (pow_le_pow_left₀ bounds.Pproj.1 (le_add_of_nonneg_right hAs) 2).trans
      (pow_le_pow_right₀ (by linarith only [hproj1, hAs]) hAsample)
  have hprojMass : r.Pproj ≤ r.Pmass :=
    (by nlinarith only [hproj1] : r.Pproj ≤ r.Pproj^2).trans hprojSqMass
  have hPmass : P ≤ r.Pmass := hPproj.trans hprojMass
  have hPsample : P ≤ r.Psample := hPmass.trans hmassSample
  have hprojSide : r.Pproj ≤ r.Pside := hprojSample.trans hsampleSide
  have hmassSide : r.Pmass ≤ r.Pside := hmassSample.trans hsampleSide
  have hPSide : P ≤ r.Pside := hPL.trans hLSide
  have hPeriodProj : ((m + 1 : ℕ) : ℝ) * Pk ≤ r.Pproj := by
    calc
      _ ≤ ((m + 1 : ℕ) : ℝ) * P := mul_le_mul_of_nonneg_left hPk (Nat.cast_nonneg _)
      _ ≤ (P + 1) * P := mul_le_mul_of_nonneg_right (by push_cast; linarith only [hmP]) hP
      _ ≤ (2 * P + 1) * P := mul_le_mul_of_nonneg_right (by linarith only [hP]) hP
      _ ≤ _ := hframeProj
  have hcoverBase : r.coverLog ≤ r.baseAmbient := by
    change r.coverLog ≤ r.Pproj + r.coverLog + r.Vlog + r.Nlog + r.Q +
      (layerTailDegree K.m + 1 : ℕ) * L + 3 * P + comparisonProfileBound + (2 ^ dim : ℕ) + 32
    have hdeg : 0 ≤ ((layerTailDegree K.m + 1 : ℕ) : ℝ) * L := by positivity
    have hprof : (0 : ℝ) ≤ comparisonProfileBound := Nat.cast_nonneg _
    have hpow : (0 : ℝ) ≤ (2^dim : ℕ) := Nat.cast_nonneg _
    linarith only [bounds.Pproj.1, bounds.Vlog.1, bounds.Nlog.1, bounds.Q.1, hdeg, hP, hprof, hpow]
  let A := 9 * (9 * (r.baseAmbient + r.idealQ) + 13) + 5
  have hA0 : 0 ≤ A := by
    dsimp only [A]
    linarith only [bounds.baseAmbient.1, bounds.idealQ.1]
  have hbaseA : r.baseAmbient ≤ A := by
    dsimp only [A]; linarith only [bounds.baseAmbient.1, bounds.idealQ.1]
  have hambient : r.ambient = 2 * affineAmbientMassLog A + 7 * A + 1 := rfl
  have hmasslog := affineAmbientMassLog_nonneg hA0
  have hbaseAmbient : r.baseAmbient ≤ r.ambient := by
    linarith only [hambient, hmasslog, hbaseA, hA0]
  have hcoverSample := hcoverBase.trans (hbaseAmbient.trans hAmbientSample)
  have hFrame : (Fintype.card (Option (Fin dim) × Fin nX) : ℝ) ≤ r.Pmass := by
    simp only [Fintype.card_prod, Fintype.card_option, Fintype.card_fin, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one]
    apply le_trans _ (hframeProj.trans hprojMass)
    exact mul_le_mul (by linarith only [hdimP, hP]) hX (Nat.cast_nonneg _)
      (by linarith only [hP])
  have hFrameProjection : (Fintype.card (Option T × Fin nX) : ℝ) ≤ r.Pproj := by
    simp only [Fintype.card_prod, Fintype.card_option, Fintype.card_fin, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one]
    apply le_trans _ hframeProj
    exact mul_le_mul (by linarith only [hT]) hX (Nat.cast_nonneg _)
      (by linarith only [hP])
  have hmPproj : (m : ℝ) * P ≤ r.Pproj := by
    calc
      _ ≤ P * P := mul_le_mul_of_nonneg_right hmP hP
      _ ≤ (2 * P + 1) * P := mul_le_mul_of_nonneg_right (by linarith only [hP]) hP
      _ ≤ _ := hframeProj
  have hmPmass : (m : ℝ) * P^2 ≤ r.Pmass := by
    calc
      _ = ((m : ℝ) * P) * P := by ring
      _ ≤ r.Pproj * r.Pproj := mul_le_mul hmPproj hPproj hP bounds.Pproj.1
      _ = r.Pproj^2 := (pow_two _).symm
      _ ≤ _ := hprojSqMass
  have hAmb : (Fintype.card (CoefficientAmbientIndex (Fin dim) J) : ℝ) ≤ r.Pmass := by
    apply ((coefficientAmbientIndex_card_from_layer_counts hP hcoeff (by simpa only [Nat.cast_sum] using hJ)).1).trans hmPmass
  have hJet : ((∑ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1)) : ℝ≥0) : ℝ≥0) : ℝ) ≤ r.Pmass := by
    exact ((coefficientAmbientIndex_card_from_layer_counts hP hcoeff (by simpa only [Nat.cast_sum] using hJ)).2.2).trans (hmPproj.trans hprojMass)
  have hTau : (Real.exp (-Pphysical))⁻¹ = Real.exp Pphysical := by rw [Real.exp_neg, inv_inv]
  have hPrecision : (Real.exp (-target))⁻¹ = Real.exp target := by rw [Real.exp_neg, inv_inv]
  have hTauMass : (Real.exp (-Pphysical))⁻¹ ≤ Real.exp r.Pmass := by
    rw [hTau]
    exact Real.exp_le_exp.mpr (hphysical.trans hPmass)
  have hTauSample : (Real.exp (-Pphysical))⁻¹ ≤ Real.exp r.Psample :=
    hTauMass.trans (Real.exp_le_exp.mpr hmassSample)
  have hPrecisionSample : (Real.exp (-target))⁻¹ ≤ Real.exp r.Psample := by
    rw [hPrecision]
    exact Real.exp_le_exp.mpr (htarget.trans hPsample)
  have hStrideProj (i : Fin nX) : (stride i : ℝ) ≤ Real.exp r.Pproj :=
    (hstride i).trans (Real.exp_le_exp.mpr (hQstride.trans hPproj))
  have hStrideMass (i : Fin nX) : (stride i : ℝ) ≤ Real.exp r.Pmass :=
    (hStrideProj i).trans (Real.exp_le_exp.mpr hprojMass)
  exact {
    sample_nonneg := bounds.Psample.1
    mass_nonneg := bounds.Pmass.1
    projection_one := hproj1
    primitive_projection := hPproj
    late_projection := hLproj
    gain_projection := hGainProj
    period_projection := hPeriodProj
    profile_projection := hprofile.trans (hPproj.trans (by linarith [Real.add_one_le_exp r.Pproj]))
    projection_mass := hprojMass
    mass_sample := hmassSample
    cover_base := hcoverBase
    cover_sample := hcoverSample
    ambient_sample := hAmbientSample
    sample_side := hsampleSide
    projection_side := hprojSide
    mass_side := hmassSide
    primitive_side := hPSide
    late_side := hLSide
    physical_side := hphysical.trans hPSide
    target_side := htarget.trans hPSide
    X_sample := by simpa only [Fintype.card_fin] using hX.trans hPsample
    frame_sample := hFrame.trans hmassSample
    ambient_dimension_sample := hAmb.trans hmassSample
    jet_sample := (hJet.trans hmassSample).trans (by linarith [Real.add_one_le_exp r.Psample])
    stride_scale_nonneg := Real.exp_nonneg _
    stride_scale_sample := Real.exp_le_exp.mpr (hQstride.trans hPsample)
    stride_sample := fun i => (hStrideMass i).trans (Real.exp_le_exp.mpr hmassSample)
    tau_pos := Real.exp_pos _
    precision_pos := Real.exp_pos _
    tau_sample := by simpa only [one_div] using hTauSample
    epsilon_sample := by simpa only [one_div] using hPrecisionSample
    eta_sample := hPrecisionSample
    X_mass := by simpa only [Fintype.card_fin] using hX.trans hPmass
    frame_mass := hFrame
    ambient_dimension_mass := hAmb
    jet_mass := hJet.trans (by linarith [Real.add_one_le_exp r.Pmass])
    stride_mass := hStrideMass
    tau_mass := by simpa only [one_div] using hTauMass
    X_projection := by simpa only [Fintype.card_fin] using hX.trans hPproj
    variables_projection := hT.trans h2Pproj
    frame_projection := hFrameProjection
    stride_projection := hStrideProj
    tau_projection := by rw [hTau]; exact Real.exp_le_exp.mpr (hphysical.trans hPproj) }

theorem preparedModularGeneralDetector_sampling_bounds_of_geometry
    {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    (rowSets : Fin m → Finset (Finset (Fin dim)))
    (selection : Fin dim ↪ G)
    (K : PreparedModularCanonicalDetectorResourceConstants) (hm : K.m = m)
    {P L D target Pphysical Qstride Pk : ℝ} (hP : 0 ≤ P) (hPL : P ≤ L)
    (hAsample : 2 ≤ K.Asample)
    (hdim : AllocatedComparisonDimensions (G := G) B (Fin dim)
      (fun j => (rowSets j : Type)) D) (hDP : D ≤ P)
    (hX : (nX : ℝ) ≤ P)
    (hJ : ((∑ j, Fintype.card (J j) : ℕ) : ℝ) ≤ (m : ℝ) * P)
    (htarget : target ≤ P) (hphysical : Pphysical ≤ P)
    (hQstride : Qstride ≤ P) (hPk : Pk ≤ P)
    (hstride : ∀ i, (stride i : ℝ) ≤ Real.exp Qstride) :
    PreparedModularGeneralDetectorSamplingBounds (dim := dim) (J := J)
      (T := LayerSamplerVariables G I n B) stride
      (preparedModularGeneralDetectorResources K dim P L) P L target Pphysical Qstride Pk := by
  apply preparedModularGeneralDetector_sampling_bounds stride K hm hP hPL hAsample
    (hdim.degree.trans hDP)
    (by simpa only [Fintype.card_fin] using hdim.cube.trans hDP) hX
  · exact (preparedModularGeneralDetector_variable_count B rowSets hdim).trans
      (mul_le_mul_of_nonneg_left hDP (by norm_num))
  · exact hJ
  · exact preparedModularGeneralDetector_jet_counts_of_geometry B selection hdim hDP
  · exact htarget
  · exact hphysical
  · exact hQstride
  · exact hPk
  · exact hstride
  · exact hdim.profile.trans hDP

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedModularGeneralDetectorLateCoarseConsumer
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m s : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type} [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

include U b o hb bW

theorem preparedModularGeneralDetector_period_prefactor {P D Pk Qstride pDetect Pnum : ℝ} {nX : ℕ}
    (hP : 0 ≤ P)
    (hdim : AllocatedComparisonDimensions (G := G) B (Fin (s + 1))
      (fun j : Fin m => (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1) : Type)) D)
    (hDP : D ≤ P) (hnX : (nX : ℝ) ≤ P) (hPk : Pk ∈ Set.Icc 0 P)
    (hQstride : Qstride ∈ Set.Icc 0 P) (hp : pDetect ∈ Set.Icc 0 P)
    (hPnum : Pnum ∈ Set.Icc 0 P) :
    let r := preparedModularCanonicalDetectorResources (preparedModularGeneralDetectorConstants m s) P
    let O := fun j : Fin m => (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1) : Type)
    let L := ((m + 1 : ℕ) : ℝ) * Pk
    let qlog := L + nX * Qstride
    let maskLog := (Fintype.card (LayerSamplerAxis I n) : ℝ) * ((m * 2 ^ (m + 1) : ℕ) * Pk) +
      ∑ j, (Fintype.card (Q j) : ℝ) * (Fintype.card (O j) * L)
    let labelLog := (∑ j, (n j : ℝ) * L) + ∑ j, (Fintype.card (Q j) : ℝ) * L
    let Fmodel := (m * (2 : ℝ) ^ Fintype.card (Fin (s + 1))) * (Pnum + 8) * (1 + 4 * Pnum) + maskLog
    P ≤ r.Q ∧ L ∈ Set.Icc 0 r.Q ∧ qlog ∈ Set.Icc 0 r.Q ∧
      maskLog ∈ Set.Icc 0 r.Q ∧ labelLog ∈ Set.Icc 0 r.Q ∧ Fmodel ∈ Set.Icc 0 r.Fpref := by
  intro r O L qlog maskLog labelLog Fmodel
  have hQ (j : Fin m) : (Fintype.card (Q j) : ℝ) ≤ P :=
    ((allocatedProfile_dimensions U b o B hdim hb bW).2 j).trans hDP
  have hn := (preparedModularGeneralDetector_layer_axes B
    (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)) hdim).2
  have haxes := hdim.axes.trans hDP
  let Cgrid := (preparedModularGeneralDetectorConstants m s).Cgrid
  obtain ⟨hPQ, hL, hq, _, hmask, hlabel, _⟩ :=
    (Classical.choose_spec (exists_preparedModularCanonicalDetector_period_budget.{0,0} m (s + 1) Cgrid)).2
      (A := LayerSamplerAxis I n) (nX := nX) n Q hP hnX hPk hQstride hp haxes (fun j => (hn j).trans hDP) hQ
  have hF := (Classical.choose_spec (exists_canonicalSlicedModelPrefactor_budget.{0,0} m (s + 1))).2
    (I := I) (n := n) (Q := Q) hP hPnum hPk haxes hQ
  refine ⟨hPQ, hL, hq, hmask, hlabel, ?_⟩
  change 0 ≤ Fmodel ∧ Fmodel ≤ _
  have heq : Fmodel = (m * (2 : ℝ) ^ Fintype.card (Fin (s + 1))) * (Pnum + 8) * (1 + 4 * Pnum) +
      Fintype.card (LayerSamplerAxis I n) * ((m * 2 ^ (m + 1) : ℕ) * Pk) +
      ∑ j, (Fintype.card (Q j) : ℝ) * (Fintype.card (O j) * L) := by
    dsimp only [Fmodel, maskLog]
    ring
  rw [heq]
  exact hF

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m s : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

theorem preparedModularGeneralDetector_late_positive_bounds
    (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (hσ1 : ∀ j, σ j ≤ 1)
    (C V : Fin m → ℝ≥0)
    (hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ C j * ‖z‖)
    (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ V j)
    (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm z‖ ≤ Cinv j * ‖z‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    {Pmaster Plate D : ℝ} (hMaster : 0 ≤ Pmaster) (hLate : Pmaster ≤ Plate)
    (hd : AllocatedComparisonDimensions (G := G) B (Fin (s + 1))
      (fun j : Fin m => (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1) : Type)) D)
    (hD : D ≤ Pmaster) {nX : ℕ} (hnX : (nX : ℝ) ≤ Pmaster)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp Pmaster)
    (hσLate : ∀ j, (σ j)⁻¹ ≤ Real.exp Plate)
    (hLLate : (S.value : ℝ) ≤ Real.exp Plate)
    (hCP : ∀ j, (C j : ℝ) ≤ Real.exp Pmaster)
    (hVP : ∀ j, (V j : ℝ) ≤ Real.exp Pmaster)
    (p : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : Fin nX → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : Fin nX → ℕ) (hs : ∀ d, 0 < stride d)
    (hsP : ∀ d, (stride d : ℝ) ≤ Real.exp Pmaster)
    {τ ξ : ℝ} (hτ : 0 < τ) (hτP : τ⁻¹ ≤ Real.exp Pmaster)
    (hτhalf : τ ≤ 1 / 2) (hτdim : (nX : ℝ) * τ ≤ 1 / 2)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hξLate : ξ⁻¹ ≤ Real.exp Plate)
    (N : Fin nX → ℕ) {rank : ℝ}
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (p j))
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride))
    (hCells : cells.Nonempty) :
    let r := preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m s) (s + 1) Pmaster Plate
    (∀ d, Real.exp r.required ≤ (N d : ℝ)) → Real.exp r.required ≤ rank →
    let W := allocatedPhysicalRootBudget B U basis S (fun _ => 0)
    let widths := narrowTrimmedSpatialWidths (G := G)
      (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let bases := trimmedIntegerBox N (spatialTrimMargin τ N)
    let density := allocatedJointBaseDensity B U basis hb o hR hσ S (Fin nX) p hm
    let Z := selectedJointDensityMass bases stride cells widths density
    ∃ (_hN : ∀ x, 0 < N x) (_hbases : bases.Nonempty) (_hbox : (integerBox N).Nonempty)
      (_hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells widths z),
    ∃ _hnormalizer : |Z - 1| ≤ Real.exp (-r.E) ∧
      Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧ 0 < Z ∧ Z⁻¹ ≤ 2,
    ∀ x, 2 * spatialTrimMargin τ N x ≤ N x := by
  intro r hSize hRank W widths bases density Z
  let K := preparedModularGeneralDetectorConstants m s
  have hproj : r.Pproj = 4 * (Plate + 8) ^ 2 := rfl
  have hPlate : 0 ≤ Plate := hMaster.trans hLate
  have hLproj : Plate ≤ r.Pproj := by
    nlinarith only [hproj, hPlate, sq_nonneg Plate]
  have hExpLate := Real.exp_le_exp.mpr hLproj
  have hPproj : Pmaster ≤ r.Pproj := by
    nlinarith only [hproj, hPlate, hLate, sq_nonneg Plate]
  have h2Pproj : 2 * Pmaster ≤ r.Pproj := by
    nlinarith only [hproj, hPlate, hLate, sq_nonneg Plate]
  have hframeProj : (2 * Pmaster + 1) * Pmaster ≤ r.Pproj := by
    have hsq : Pmaster^2 ≤ Plate^2 := pow_le_pow_left₀ hMaster hLate 2
    nlinarith only [hproj, hPlate, hLate, hsq, sq_nonneg Plate]
  have hExp := Real.exp_le_exp.mpr hPproj
  have hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ 2 * Pmaster :=
    (preparedModularGeneralDetector_variable_count B
      (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)) hd).trans (by linarith only [hD])
  have hframe : (Fintype.card (Option (LayerSamplerVariables G I n B) × Fin nX) : ℝ) ≤ r.Pproj := by
    rw [Fintype.card_prod, Fintype.card_option, Fintype.card_fin, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    exact (mul_le_mul (add_le_add_left hvars 1) hnX (Nat.cast_nonneg _) (by positivity)).trans
      (by simpa only [add_comm] using hframeProj)
  obtain ⟨hI, hn⟩ := preparedModularGeneralDetector_layer_axes B
    (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)) hd
  have hJ (j : Fin m) : (Fintype.card (J j) : ℝ) ≤ r.Pproj :=
    (Nat.cast_le.mpr (allocatedAmbientDimension_le_axes U basis o j)).trans
      (hd.axes.trans (hD.trans hPproj))
  have hW := allocatedPhysicalRootBudget_nonneg B U basis S (fun _ => 0)
  have hWproj : W ≤ Real.exp r.Pproj :=
    (preparedModularGeneralDetector_physical_root B
      (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)) U basis S hd (hD.trans hLate) hLLate).trans
        (Real.exp_le_exp.mpr (by nlinarith only [hproj, hPlate, hLate, sq_nonneg Plate]))
  have bounds := ((Classical.choose_spec
    (exists_preparedModularGeneralDetector_resource_budget K (s + 1))).2 hMaster hLate).1
  have hRequired := (preparedModularGeneralDetector_required_bounds K (s + 1) hMaster hLate).2.2.2.2
  have hFull : (max r.Pproj r.E + K.Amarginal) ^ K.Amarginal ≤ r.required := by
    apply le_trans _ hRequired
    apply pow_le_pow_left₀
      (add_nonneg (le_max_of_le_left bounds.Pproj.1) (Nat.cast_nonneg _))
    exact add_le_add
      (max_le (le_add_of_nonneg_right bounds.E.1) (le_add_of_nonneg_left bounds.full.1)) le_rfl
  exact allocated_fullBox_positive_law_at_model_budget m B U basis S hb o μ ν hR hσ hσ1
    C V hC hV Cinv hCinv hchart hsmall
    (P := r.Pproj) (E := r.E) (hMaster.trans hPproj) (hd.degree.trans (hD.trans hPproj))
    (hvars.trans h2Pproj) (by simpa only [Fintype.card_fin] using hnX.trans hPproj) hframe
    (fun j => (hRP j).trans hExp) (fun j => (hσLate j).trans hExpLate)
    (fun j => (hd.coefficients j).trans (hD.trans hPproj))
    (fun j => (hI j).trans (hD.trans hPproj)) (fun j => (hn j).trans (hD.trans hPproj)) hJ
    ((hd.profile.trans (hD.trans hPproj)).trans (by linarith [Real.add_one_le_exp r.Pproj]))
    (hLLate.trans hExpLate) (fun j => (hCP j).trans hExp) (fun j => (hVP j).trans hExp)
    p hp hm stride hs (fun d => (hsP d).trans hExp) hW hWproj le_rfl
    hτ (hτP.trans hExp) hτhalf (by simpa only [Fintype.card_fin] using hτdim)
    hξ hξ1 (hξLate.trans hExpLate) N
    (fun d => (Real.exp_le_exp.mpr hFull).trans (hSize d)) hrank
    ((Real.exp_le_exp.mpr hFull).trans hRank) cells hCells

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PreparedModularGeneralDetectorFreeSpatialBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem preparedModularGeneralDetector_free_spatial_bounds
    (K : PreparedModularCanonicalDetectorResourceConstants) (dim : ℕ)
    {P L Pphysical τ : ℝ} (hP : 0 ≤ P) (hPL : P ≤ L)
    (hAsample : 2 ≤ K.Asample) (hphysical : Pphysical ≤ P)
    (hτ : 0 < τ) (hτinv : τ⁻¹ ≤ Real.exp Pphysical) :
    PreparedModularGeneralDetectorFreeSpatialBounds
      (preparedModularGeneralDetectorResources K dim P L) τ := by
  let r := preparedModularGeneralDetectorResources K dim P L
  obtain ⟨_, _, hPnative, _, _, _, hprojSample, _, hLSide, _⟩ :=
    preparedModularGeneralDetectorResources_primitive_domination K dim hP hPL
  have hL : 0 ≤ L := hP.trans hPL
  have hproj : r.Pproj = 4 * (L + 8)^2 := rfl
  have hproj1 : 1 ≤ r.Pproj := by nlinarith only [hproj, hL, sq_nonneg L]
  have hPproj : P ≤ r.Pproj := by nlinarith only [hproj, hL, hPL, sq_nonneg L]
  have hprojMass : r.Pproj ≤ r.Pmass := by
    change r.Pproj ≤ (r.Pproj + K.Asample)^K.Asample
    have hAs : (0 : ℝ) ≤ K.Asample := Nat.cast_nonneg _
    have hsq : r.Pproj ≤ r.Pproj^2 := by nlinarith only [hproj1]
    exact hsq.trans ((pow_le_pow_left₀ (by linarith only [hproj1])
      (le_add_of_nonneg_right hAs) 2).trans
      (pow_le_pow_right₀ (by linarith only [hproj1, hAs]) hAsample))
  have hprojection : τ⁻¹ ≤ Real.exp r.Pproj :=
    hτinv.trans (Real.exp_le_exp.mpr (hphysical.trans hPproj))
  exact {
    tau_pos := hτ
    tau_sample := by simpa only [one_div] using
      hprojection.trans (Real.exp_le_exp.mpr hprojSample)
    tau_mass := by simpa only [one_div] using
      hprojection.trans (Real.exp_le_exp.mpr hprojMass)
    tau_projection := hprojection
    tau_native := hτinv.trans (Real.exp_le_exp.mpr (hphysical.trans hPnative))
    tau_side := hτinv.trans (Real.exp_le_exp.mpr (hphysical.trans (hPL.trans hLSide))) }

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SharedWidthPreparedModularGeneralDirectDetectionFreeTrim
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem preparedModularGeneralDetector_required_sharedWidth_side
    (K : PreparedModularCanonicalDetectorResourceConstants) (dim : ℕ)
    (hAproj : 1 ≤ K.Aproj) {P L : ℝ} (hP : 0 ≤ P) (hPL : P ≤ L) :
    let r := preparedModularGeneralDetectorResources K dim P L
    (r.Pside + K.Aside) ^ K.Aside + r.Pproj ≤ r.required := by
  intro r
  have hL : 0 ≤ L := hP.trans hPL
  have h := ((Classical.choose_spec
    (exists_preparedModularGeneralDetector_resource_budget K dim)).2 hP hPL).1
  have hproj : 1 ≤ r.Pproj := by
    change 1 ≤ 4 * (L + 8) ^ 2
    nlinarith [sq_nonneg L]
  have hbase : 1 ≤ r.Pproj + K.Aproj := by
    exact hproj.trans (le_add_of_nonneg_right (Nat.cast_nonneg _))
  have hprojTerm : r.Pproj ≤ (r.Pproj + K.Aproj) ^ K.Aproj :=
    (le_add_of_nonneg_right (Nat.cast_nonneg _)).trans
      (le_self_pow₀ hbase (by omega))
  have hs := h.Psample.1
  have hm := h.Pmass.1
  have hf := h.full.1
  have he := h.E.1
  have h1 : 0 ≤ (r.Psample + K.Apert) ^ K.Apert := by positivity
  have h2 : 0 ≤ (r.Pmass + K.AmassWindow) ^ K.AmassWindow := by positivity
  have h5 : 0 ≤ (r.full + r.E + K.Amarginal) ^ K.Amarginal := by positivity
  have hsum : r.required = (r.Psample + K.Apert) ^ K.Apert +
      (r.Pmass + K.AmassWindow) ^ K.AmassWindow + (r.Pproj + K.Aproj) ^ K.Aproj +
      (r.Pside + K.Aside) ^ K.Aside + (r.full + r.E + K.Amarginal) ^ K.Amarginal := rfl
  linarith only [hsum, hprojTerm, h1, h2, h5]

theorem preparedModularGeneralDetectorConstants_required_sharedWidth_side
    (m s dim : ℕ) {P L : ℝ} (hP : 0 ≤ P) (hPL : P ≤ L) :
    let K := preparedModularGeneralDetectorConstants m s
    let r := preparedModularGeneralDetectorResources K dim P L
    (r.Pside + K.Aside) ^ K.Aside + r.Pproj ≤ r.required := by
  have hAproj : 2 ≤ (preparedModularGeneralDetectorConstants m s).Aproj :=
    (Classical.choose_spec (Classical.choose_spec
      (exists_allocated_canonical_constructed_projection.{0,0,0,0,0} m (s + 1)))).2.1
  exact preparedModularGeneralDetector_required_sharedWidth_side
    (preparedModularGeneralDetectorConstants m s) dim (by omega) hP hPL

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

variable {m s : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {nX : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (Fin.val j + 1))
attribute [local instance 2000] fullBooleanRowSetFintype
attribute [local instance] ScalarSiteExpansion.termFinite
variable (selection : Fin (s + 1) ↪ G) (stride N : Fin nX → ℕ) [∀ i, NeZero (N i)]
variable (Pdetect : Polynomial ℕ) (u pModel pSlice : ℝ) (Vtail : Fin m → ℝ≥0)
local notation "pDetect" => allocatedModelTestLog u pModel
variable (α τ : ℝ)
variable {P : ℝ}

variable (Q : Fin m → Type) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]

variable [CompactSpace (CoefficientTorus (K := Fin (s + 1)) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin (s + 1)) U)]
variable [BorelSpace (CoefficientTorus (K := Fin (s + 1)) U)]
variable (μrows : Measure (CoefficientTorus (K := Fin (s + 1)) U))
variable [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]

variable [MeasurableSpace (SiteTorus (Finset (Fin (s + 1))) U)]
variable [BorelSpace (SiteTorus (Finset (Fin (s + 1))) U)]

include hb o bW μ ν μrows hR hσ in
theorem preparedModularGeneralDirectDetectionFreeTrimSharedWidthInterface_of_geometry (hsm : s ≤ m)
    (Pchart D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget : ℝ) (K : ℝ≥0)
    (geometry : AllocatedEarlyNativeSourceGeometryGeneral (s := s) (B := B) (U := U) (basis := basis)
      (S := S) (nX := nX) Pchart P D target Pk Prho Qstride pDetect K) :
    PreparedModularGeneralDirectDetectionFreeTrimSharedWidthInterface
      (B := B) (U := U) (basis := basis) (hR := hR) (hσ := hσ) (S := S)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (u := u) (pModel := pModel) (pSlice := pSlice) (Vtail := Vtail) (α := α) (τ := τ)
      (hb := hb) (o := o)
      Pchart P D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget K := by
  intro hLate hMaster hDMaster hPkMaster hQstrideMaster hDetectMaster hnXMaster hRone
    hRiMaster hσiLate hSLate hKMaster hcutoffMaster hMkP hMkPk hstride hstrideBound
    C hC hCbound hchart Cforward hforward hForwardMaster hVtailMaster hVactual hBa hBi
    huMaster hModelMaster hSliceModel hcountModel hαlower hαone
    hPrhoMaster htargetMaster hGainMaster hCoarseMaster hCoarseLower hCoarseLate hPhysicalMaster hmPhysical hDimPhysical
    hvarsPhysical hXPhysical hPkPhysical hQstridePhysical hGainLog hprecision _hXiLog
    hτSpatial hτinv r W ξn hξn hξn_le hξLate hW cells poly hp hmem Rrank hNlarge hrank hRankLarge V
  let constants := preparedModularGeneralDetectorConstants m s
  have hd := geometry.hdimensions
  have hmMaster : (m : ℝ) ≤ Pmaster := hd.degree.trans hDMaster
  have hJ := (allocatedProfile_dimensions U basis o B hd hb bW).1
  have hJMaster (j : Fin m) : (Fintype.card (J j) : ℝ) ≤ Pmaster := (hJ j).trans hDMaster
  have hvarsMaster : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Pmaster :=
    hvarsPhysical.trans hPhysicalMaster.2
  have hAsample : 2 ≤ constants.Asample :=
    (Classical.choose_spec (exists_allocatedCanonicalProjection_composed_budget m (s + 1)
      constants.Acover)).1
  have sampling := preparedModularGeneralDetector_sampling_bounds_of_geometry
    (J := J) stride B rowSets selection constants rfl hMaster hLate hAsample hd hDMaster
    hnXMaster (preparedModularGeneralDetector_ambient_count hJMaster) htargetMaster.2
    hPhysicalMaster.2 hQstrideMaster.2 hPkMaster.2 hstrideBound
  have freeSpatial := preparedModularGeneralDetector_free_spatial_bounds constants (s + 1)
    hMaster hLate hAsample hPhysicalMaster.2 hτSpatial hτinv
  have bounds := ((Classical.choose_spec
    (exists_preparedModularGeneralDetector_resource_budget constants (s + 1))).2 hMaster hLate).1
  obtain ⟨hDn, hgridn, hvn, hFn, hBn, hPnative, hprimitiveNative⟩ :=
    preparedModularGeneralDetector_native_inputs constants (s + 1) hMaster hLate
  obtain ⟨_, _, hQlog, _, _, hFmodel⟩ :=
    preparedModularGeneralDetector_period_prefactor B U basis o hb bW hMaster hd hDMaster
      hnXMaster hPkMaster hQstrideMaster hDetectMaster ⟨hMaster, le_rfl⟩
  have hgrid := preparedModularGeneralDetector_grid_resource_width_bound constants (s + 1)
    hMaster hLate hDetectMaster hQlog
  have hEarlyCoarse : pGain + 32 ∈ Set.Icc 0 Pmaster :=
    ⟨by linarith only [hGainMaster.1], hCoarseMaster⟩
  have hCoarse0 : 0 ≤ coarseTarget := hEarlyCoarse.1.trans hCoarseLower
  have hAmbient := preparedModularGeneralDetector_ambient_bound constants (s + 1) hMaster
    (hd.outputs.trans hDMaster) ⟨bounds.Pbox.1, le_rfl⟩ hPrhoMaster
    ⟨bounds.Vlog.1, le_rfl⟩ ⟨bounds.Nlog.1, le_rfl⟩ ⟨bounds.Q.1, le_rfl⟩ htargetMaster
    ⟨bounds.baseAmbient.1, le_rfl⟩
  have hMkPhysical := hMkPk.trans (Real.exp_le_exp.mpr hPkPhysical)
  have hGPhysical : (Fintype.card G : ℝ) ≤ Pphysical :=
    (Nat.cast_le.mpr (allocatedKernelVariables_card_le_variables (G := G) B)).trans hvarsPhysical
  have hXiProj : ξn⁻¹ ≤ Real.exp r.Pproj :=
    hξLate.trans (Real.exp_le_exp.mpr sampling.late_projection)
  have hRoot := preparedModularDetector_physical_root_of_variables B U basis S (hMaster.trans hLate)
    (hvarsMaster.trans hLate) hSLate
  have hRootLog : 2 * Plate + 8 ≤ r.Pproj := by
    change 2 * Plate + 8 ≤ 4 * (Plate + 8)^2
    nlinarith only [hMaster.trans hLate, sq_nonneg Plate]
  have hWproj : W ≤ Real.exp r.Pproj := hRoot.trans (Real.exp_le_exp.mpr hRootLog)
  have hExpProj : Real.exp Pmaster ≤ Real.exp r.Pproj :=
    Real.exp_le_exp.mpr sampling.primitive_projection
  have hGain := allocatedDetectedGain_lower s
    (Fintype.card (LayerSamplerVariables G I n B)) Pdetect hαlower hGainLog
  obtain ⟨hReqSample, hReqMass, hReqProj, _hReqSide, _⟩ :=
    preparedModularGeneralDetector_required_bounds constants (s + 1) hMaster hLate
  have hReqSideShared := preparedModularGeneralDetectorConstants_required_sharedWidth_side
    m s (s + 1) hMaster hLate
  have hSize (x : ℝ) (hx : x ≤ r.required) (i : Fin nX) : Real.exp x ≤ (N i : ℝ) :=
    (Real.exp_le_exp.mpr hx).trans (hNlarge i)
  have hRank (x : ℝ) (hx : x ≤ r.required) : Real.exp x ≤ Rrank :=
    (Real.exp_le_exp.mpr hx).trans hRankLarge
  have hNative := preparedModularGeneralDirectDetectionAmbient_sharedWidth_s2 (ξn := ξn)
    (B := B) (U := U) (basis := basis) (hR := hR) (hσ := hσ) (S := S)
    (selection := selection) (stride := stride) (N := N)
    (Pdetect := Pdetect) (u := u) (pModel := pModel) (pSlice := pSlice) (Vtail := Vtail) (α := α)
    (Q := Q) (hb := hb) (o := o) (bW := bW) (ν := ν) (μ := μ) (μrows := μrows)
    hsm Pchart D target Pk Prho Qstride K geometry hLate hMaster hDMaster hPkMaster hQstrideMaster
    hDetectMaster hnXMaster hRone hRiMaster hSLate hKMaster hcutoffMaster
    hMkP hMkPk hstride hstrideBound C hC hCbound hchart Cforward hforward
    hForwardMaster hVtailMaster hVactual hBa hBi
    (Pproj := r.Pproj) (coarseTarget := coarseTarget) (Ecoarse := pGain + 32) (pGain := pGain)
    (τ := τ) (Pphysical := Pphysical) (Pnative := r.Pnative) (Pside := r.Pside)
    hξn hξn_le cells poly hp hmem
    (lossTarget := pGain + 32) (Psample := r.Psample) (Rrank := Rrank)
    (Sstride := Real.exp Qstride) (εsample := Real.exp (-target)) (ηsample := Real.exp (-target))
    hstride (fun i => Nat.pos_of_ne_zero (NeZero.ne (N i))) hτSpatial sampling.sample_nonneg
    sampling.X_sample sampling.frame_sample sampling.stride_scale_nonneg sampling.stride_scale_sample
    sampling.precision_pos freeSpatial.tau_sample sampling.epsilon_sample hstrideBound
    (hSize _ hReqSample) hrank (hRank _ hReqSample) sampling.precision_pos
    sampling.ambient_dimension_sample (by simpa only [Fintype.card_fin] using (hAmbient.2.2.trans sampling.ambient_sample))
    sampling.jet_sample sampling.eta_sample hPhysicalMaster.1 hMkPhysical hmPhysical hCoarse0
    hDimPhysical hGPhysical (by simpa only [Fintype.card_fin] using hXPhysical)
    hprecision le_rfl le_rfl
  have hNative := hNative
    (hMaster.trans hPnative) hDn
    (by change 0 ≤ _ ∧ _ ≤ _
        have hCgrid : constants.Cgrid = Classical.choose
            (exists_preparedModularCanonicalDetector_grid_parameters.{0} m (s + 1) canonicalTransitionLip) := rfl
        rw [← hCgrid]
        simpa only [Nat.cast_add, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, zero_add, one_add_one_eq_two]
          using And.intro hgrid.1 (hgrid.2.trans hgridn.2)) hvn
    (by change 0 ≤ _ ∧ _ ≤ _
        simpa only [add_assoc] using And.intro hFmodel.1 (hFmodel.2.trans hFn.2))
    (hprimitiveNative _ hPrhoMaster) (hprimitiveNative _ hPkMaster)
    (hprimitiveNative _ htargetMaster) hBn (hprimitiveNative _ hPhysicalMaster)
    (hprimitiveNative _ hEarlyCoarse) (hprimitiveNative _ hGainMaster)
    (fun i => (hstrideBound i).trans (Real.exp_le_exp.mpr hQstridePhysical))
    (by simpa only [one_div] using hτinv)
    hGain (by linarith only [hGainMaster.2, sampling.gain_projection]) hCoarseLower le_rfl le_rfl
    Cforward sampling.cover_base sampling.cover_sample sampling.mass_sample hforward hVactual
    sampling.X_mass sampling.frame_mass sampling.stride_mass freeSpatial.tau_mass
    (hSize _ hReqMass) (hRank _ hReqMass) sampling.ambient_dimension_mass sampling.jet_mass
    (hvarsPhysical.trans (by linarith only [Real.add_one_le_exp Pphysical]))
    sampling.projection_one (hmMaster.trans sampling.primitive_projection)
    ((hd.kernel_variables.trans hDMaster).trans sampling.primitive_projection)
    (hSLate.trans (Real.exp_le_exp.mpr sampling.late_projection)) sampling.period_projection sampling.variables_projection hWproj
    (fun j => (hRiMaster j).trans hExpProj) (fun j => (hσiLate j).trans (Real.exp_le_exp.mpr sampling.late_projection))
    (fun j => ((hd.coefficients j).trans hDMaster).trans sampling.primitive_projection)
    (fun j => (((preparedModularGeneralDetector_layer_axes B rowSets hd).1 j).trans hDMaster).trans sampling.primitive_projection)
    (fun j => (((preparedModularGeneralDetector_layer_axes B rowSets hd).2 j).trans hDMaster).trans sampling.primitive_projection)
    (fun j => (hJMaster j).trans sampling.primitive_projection) sampling.profile_projection
    (fun j => (hForwardMaster j).trans hExpProj) (fun j => (hVtailMaster j).trans hExpProj)
    sampling.X_projection sampling.frame_projection sampling.stride_projection freeSpatial.tau_projection
    hXiProj (hSize _ hReqProj) (hRank _ hReqProj)
  have hNative := hNative sampling.projection_side sampling.mass_side
    sampling.physical_side (hCoarseLate.trans sampling.late_side) (hSize _ hReqSideShared)
  intro hCells bases hbases hmass htotal Path pathLaw sides Sites e
    Tests _ Ldetect _ _ dims _ _ _ _ Ddetect Vdetect slices cdetect stepdetect Hdetect
    hstep hslices hdense hdimensionDetect hcomplexity hcap hGdetect hkernel budget
    signal hsignal hzero hdetected
  exact hNative hCells hbases hmass htotal Ddetect Vdetect slices cdetect stepdetect Hdetect
    hstep hslices hdense hdimensionDetect hcomplexity hcap hGdetect hkernel
    huMaster.1 hModelMaster.1 hSliceModel hcountModel hαlower hαone signal hsignal hzero hdetected

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PreparedUniformDegreeDirectMasterBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

section Consumer

variable {m s : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {nX : ℕ}
attribute [local instance 2000] fullBooleanRowSetFintype
attribute [local instance] ScalarSiteExpansion.termFinite
variable (selection : Fin (s + 1) ↪ G) (stride N : Fin nX → ℕ)
variable (Pdetect : Polynomial ℕ) (u pModel pSlice : ℝ) (Vtail : Fin m → ℝ≥0)
local notation "pDetect" => allocatedModelTestLog u pModel
variable (α τ : ℝ)
variable {P : ℝ}

variable (Q : Fin m → Type) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]

variable [CompactSpace (CoefficientTorus (K := Fin (s + 1)) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin (s + 1)) U)]
variable [BorelSpace (CoefficientTorus (K := Fin (s + 1)) U)]
variable (μrows : Measure (CoefficientTorus (K := Fin (s + 1)) U))
variable [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]

variable [MeasurableSpace (SiteTorus (Finset (Fin (s + 1))) U)]
variable [BorelSpace (SiteTorus (Finset (Fin (s + 1))) U)]

include hb o bW μ ν μrows hR hσ in

theorem preparedUniformDegreeDirectSource_of_geometry_s2_oai (hsm : s ≤ m)
    (Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget pRadius : ℝ)
    (scalar : PreparedUniformDegreeDirectScalarBounds m s nX
      (Fintype.card (LayerSamplerVariables G I n B))
      (sampledSupportedSlicedDetectionConstant s Pdetect)
      Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget
      pRadius u pModel pSlice)
    (geometryAt : PreparedUniformDegreeGeometryAt B U basis S s
      (sampledSupportedSlicedDetectionConstant s Pdetect) nX
      Pchart Pscale D target Pk Prho Qstride pDetect pRadius
      (2 * u + 4 * pModel + 7) pGain)
    (hRone : ∀ j, R j ≤ 1)
    (hRinv : ∀ j, (R j)⁻¹ ≤ Real.exp pRadius)
    (hσone : ∀ j, σ j ≤ 1)
    (hSLate : (S.value : ℝ) ≤ Real.exp Plate)
    (hBa : ∀ j i, positiveModerateSpectrumBlockCount j.val
      (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card
      ((layerTailDegree m + 1) * (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card)
        ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    (hBi : ∀ j i, uniformSpectrumBlockCount j.val
      (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card
      ((j.val + 1) * (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card)
        ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    (hcapacity : (s + 1) * (s + 3) ≤ Fintype.card G)
    (hαlower : Real.exp (-(2 * u + 4 * pModel + 7)) ≤ α) (hαone : α ≤ 1) :
    PreparedModularGeneralDirectDetectionFreeTrimPreparedSharedWidthInterface
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (u := u) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (α := α) (τ := τ) (hb := hb) (o := o)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget := by
  obtain ⟨⟨geometry⟩, hgainKernel⟩ := geometryAt
  intro hstride hstrideBound Cchart hCchart hCchartBound hchart Cforward hforward
    hForward hVtail hVactual _hprofile hcutoff hτfree hτfreeInv hτfreeHalf hτfreeDim
    r W ξn hξn hξle hξInvLate hW cells poly hp hmem Rrank hNlarge hrank hRankLarge V
    hcells bases Z
  have hExpMaster : Real.exp Pchart ≤ Real.exp Pmaster :=
    Real.exp_le_exp.mpr scalar.chart_master
  have hRiMaster (j) := (hRinv j).trans (Real.exp_le_exp.mpr scalar.radius_master)
  have hσLate (j) := (geometry.hσi j).trans (Real.exp_le_exp.mpr scalar.scale_late)
  have hτInvMaster : τ⁻¹ ≤ Real.exp Pmaster :=
    hτfreeInv.trans (Real.exp_le_exp.mpr scalar.physical_master.2)
  have hξone := hξle.trans (preparedModularCanonicalDetector_narrow_width_le_one (Fin nX)
    (PrincipalTupleIndex B (layerSamplerDegree I n)) selection
    (allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B))
      Pdetect pDetect pDetect α) Pphysical coarseTarget)
  obtain ⟨hNpos, hbases, hbox, hmass, hnormalizer, hmargin⟩ :=
    preparedModularGeneralDetector_late_positive_bounds B U basis S hb o μ ν hR hσ
      hσone Cforward Vtail hforward hVactual Cchart hCchart hchart
      (geometry.hbudgets Cchart hCchart hCchartBound).1 scalar.master_nonneg scalar.late
      geometry.hdimensions scalar.dimension_master scalar.ambient_master
      hRiMaster hσLate hSLate
      (fun j => (hForward j).trans hExpMaster) (fun j => (hVtail j).trans hExpMaster)
      poly hp hmem stride hstride
      (fun i => (hstrideBound i).trans (Real.exp_le_exp.mpr scalar.stride_master.2))
      hτfree hτInvMaster hτfreeHalf hτfreeDim hξn hξone hξInvLate
      N hrank cells hcells hNlarge hRankLarge
  let : ∀ i, NeZero (N i) := fun i => ⟨(hNpos i).ne'⟩
  have hMk := (hgainKernel α hαlower).2
  have hMkPk : (allocatedDetectedKernelCutoff s G
      (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect pDetect α : ℝ)
      ≤ Real.exp Pk := hMk.1
  have hMkP := hMkPk.trans (Real.exp_le_exp.mpr scalar.kernel_scale)
  have hKMaster : (Real.toNNReal (Real.exp pRadius) : ℝ) ≤ Real.exp Pmaster := by
    rw [Real.coe_toNNReal (Real.exp pRadius) (Real.exp_pos _).le]
    exact Real.exp_le_exp.mpr scalar.radius_master
  have consumer := preparedModularGeneralDirectDetectionFreeTrimSharedWidthInterface_of_geometry
    (B := B) (U := U) (basis := basis) (hR := hR) (hσ := hσ) (S := S) (P := Pscale)
    (selection := selection) (stride := stride) (N := N)
    (Pdetect := Pdetect) (u := u) (pModel := pModel) (pSlice := pSlice)
    (Vtail := Vtail) (α := α) (τ := τ)
    (Q := Q) (hb := hb) (o := o) (bW := bW) (μ := μ) (ν := ν) (μrows := μrows)
    hsm Pchart D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget
    (Real.toNNReal (Real.exp pRadius)) geometry
  have completed := consumer scalar.late scalar.master_nonneg scalar.dimension_master
    scalar.kernel_master scalar.stride_master scalar.detect_master scalar.ambient_master
    hRone hRiMaster hσLate hSLate hKMaster (hcutoff.trans hExpMaster) hMkP hMkPk
    hstride hstrideBound Cchart hCchart hCchartBound hchart Cforward hforward
    (fun j => (hForward j).trans hExpMaster) (fun j => (hVtail j).trans hExpMaster) hVactual
    hBa hBi scalar.u_master scalar.model_master scalar.slice_model scalar.count_model hαlower hαone
    scalar.rho_master scalar.target_master scalar.gain_master scalar.coarse_master
    scalar.coarse_lower scalar.coarse_late scalar.physical_master scalar.degree_physical
    scalar.detector_physical scalar.variables_physical scalar.ambient_physical
    scalar.kernel_physical scalar.stride_physical scalar.gain_log scalar.precision scalar.xi_late
    hτfree hτfreeInv hξn hξle hξInvLate
  refine ⟨hNpos, hbases, hbox, hmass, hnormalizer, hmargin, ?_⟩
  intro Path pathLaw sides Sites e Tests _ Ldetect _ _ dims _ _ _ _
    Ddetect Vdetect slices cdetect stepdetect Hdetect hstep hboxDetect hdense hcount hcomplexity hnorm
    budget'
  exact completed cells poly hp hmem hNlarge hrank hRankLarge hcells hbases hmass
    hnormalizer.2.2.1 Ddetect Vdetect slices cdetect stepdetect Hdetect hstep hboxDetect hdense hcount
    hcomplexity hnorm hcapacity hMk.2

end Consumer
end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.preparedUniformDegreeDirectSource_of_geometry_s2_oai := @OAI.Erdos3.VectorPolynomial.preparedUniformDegreeDirectSource_of_geometry_s2_oai
