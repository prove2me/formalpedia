-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.exists_preparedSourceSlicedForecastNumerics_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T07:24:38.440002+00:00
-- url     : https://prove2.me/submissions/472df26e-9069-428e-8dcb-a419ad2a08f1

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B272
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_actualFixedSpatialSlicedForecastNumerics_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedSiteWindowLogBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] (rowSets : Fin m → Finset (Finset α))
variable {D : ℝ} (h : AllocatedComparisonDimensions (G := G) B α (fun j => (rowSets j : Type _)) D)

include h

theorem allocatedIntegerAxes_card_le :
    (Fintype.card (Σ j : Fin m, Fin (n j)) : ℝ) ≤ D := by
  apply le_trans _ h.axes
  apply Nat.cast_le.mpr
  simp only [LayerSamplerAxis, Fintype.card_sigma, Fintype.card_sum, Fintype.card_fin]
  exact Finset.sum_le_sum (fun _ _ => Nat.le_add_left _ _)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ActualForecastModelPrecision
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators NNReal

theorem forecast_spatial_coordinate_exp_bound {τ Pτ : ℝ}
    (hτ : 0 < τ) (hPτ : 0 ≤ Pτ) (hτinv : τ⁻¹ ≤ Real.exp Pτ) :
    (max ⟨8 / τ, by positivity⟩ 1 : ℝ≥0) ≤
      ⟨Real.exp (Pτ + 8), Real.exp_nonneg _⟩ := by
  change max (8 / τ) (1 : ℝ) ≤ Real.exp (Pτ + 8)
  apply max_le
  · have h8 : (8 : ℝ) ≤ Real.exp 8 := by linarith [Real.add_one_le_exp (8 : ℝ)]
    rw [div_eq_mul_inv, Real.exp_add]
    exact (mul_le_mul_of_nonneg_left hτinv (by norm_num)).trans
      (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left h8 (Real.exp_nonneg Pτ))
  · exact Real.one_le_exp_iff.mpr (by linarith)

theorem forecast_ambient_coordinate_cutoff_exp_bounds
    {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {Axis : Type*} [Fintype Axis]
    (forward : Fin m → ℝ≥0) (K r : ℝ≥0)
    {D PK PF : ℝ} (_hD : 0 ≤ D) (_hPK : 0 ≤ PK) (_hPF : 0 ≤ PF)
    (hdim : (∑ j, Fintype.card (J j) : ℕ) ≤ D)
    (haxes : (Fintype.card Axis : ℝ) ≤ D)
    (hforward : ∀ j, (forward j : ℝ) ≤ Real.exp PF)
    (hK : (K : ℝ) ≤ Real.exp PK) (hr : 1 ≤ r) :
    let Lcoord := K * ∑ j, forward j * Fintype.card (J j)
    let Lcut := (Fintype.card Axis * normalizedSiteCutoffBound / (2 * r)) * Lcoord
    (Lcoord : ℝ) ≤ Real.exp (PK + PF + D) ∧
    (Lcut : ℝ) ≤ Real.exp (PK + PF + 2 * D + normalizedSiteCutoffBound + 1) := by
  intro Lcoord Lcut
  have hDexp : D ≤ Real.exp D := by linarith [Real.add_one_le_exp D]
  have hsum : (∑ j, (forward j : ℝ) * Fintype.card (J j)) ≤ Real.exp PF * D := by
    calc
      _ ≤ ∑ j, Real.exp PF * Fintype.card (J j) :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hforward j) (Nat.cast_nonneg _))
      _ = Real.exp PF * (∑ j, (Fintype.card (J j) : ℝ)) := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (by exact_mod_cast hdim) (Real.exp_nonneg _)
  have hc : (Lcoord : ℝ) ≤ Real.exp (PK + PF + D) := by
    dsimp only [Lcoord]
    simp only [NNReal.coe_mul, NNReal.coe_sum, NNReal.coe_natCast]
    calc
      _ ≤ Real.exp PK * (Real.exp PF * D) :=
        mul_le_mul hK hsum (by positivity) (Real.exp_nonneg _)
      _ ≤ Real.exp PK * (Real.exp PF * Real.exp D) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hDexp (Real.exp_nonneg _)) (Real.exp_nonneg _)
      _ = _ := by simp only [Real.exp_add]; ring
  refine ⟨hc, ?_⟩
  have hr' : (1 : ℝ) ≤ 2 * (r : ℝ) := by exact_mod_cast (show (1 : ℝ≥0) ≤ 2 * r by nlinarith)
  have hq : ((Fintype.card Axis * normalizedSiteCutoffBound / (2 * r) : ℝ≥0) : ℝ) ≤
      Real.exp (D + normalizedSiteCutoffBound + 1) := by
    change (Fintype.card Axis : ℝ) * normalizedSiteCutoffBound / (2 * (r : ℝ)) ≤ _
    have hb : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp (normalizedSiteCutoffBound + 1) := by
      linarith [Real.add_one_le_exp ((normalizedSiteCutoffBound : ℝ) + 1)]
    calc
      _ ≤ (Fintype.card Axis : ℝ) * normalizedSiteCutoffBound :=
        div_le_self (by positivity) hr'
      _ ≤ Real.exp D * Real.exp (normalizedSiteCutoffBound + 1) :=
        mul_le_mul (haxes.trans hDexp) hb (NNReal.coe_nonneg _) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  change ((Fintype.card Axis * normalizedSiteCutoffBound / (2 * r) : ℝ≥0) : ℝ) * (Lcoord : ℝ) ≤ _
  calc
    _ ≤ Real.exp (D + normalizedSiteCutoffBound + 1) * Real.exp (PK + PF + D) :=
      mul_le_mul hq hc (NNReal.coe_nonneg _) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ActualFixedSpatialSlicedPrimitiveGeometry
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {A : Type} [Fintype A]
variable {Dmod : ℕ} {selected : A → Σ j : Fin m, Fin (n j)}
variable {τ δslice : ℝ}

namespace ActualFixedSpatialForecastSetup
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout) B U b S Dmod selected τ δslice)

omit [DecidableEq X] in
theorem sliced_primitive_geometry_bounds (hR : ∀ j, 0 < R j) :
    1 ≤ s.slicedGeometryDimension ∧
    (Fintype.card A : ℝ) ≤ s.slicedGeometryDimension ∧
    (∀ a, (((selected a).1.val + 1 : ℕ) : ℝ) ≤ s.slicedGeometryDimension) ∧
    ((layerTailDegree m + 1 : ℕ) : ℝ) ≤ s.slicedGeometryDimension ∧
    (∀ a, (Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩) : ℝ) ≤ s.slicedGeometryDimension) ∧
    0 ≤ s.slicedGeometryRadiusLog ∧
    (∀ a, 0 < R (selected a).1) ∧
    (∀ a, R (selected a).1 ≤ Real.exp s.slicedGeometryRadiusLog) ∧
    (∀ a, (R (selected a).1)⁻¹ ≤ Real.exp s.slicedGeometryRadiusLog) ∧
    (∀ a, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1)) : ℝ) ≤ Real.exp s.slicedGeometryRadiusLog) := by
  have hP0 : 0 ≤ s.P := zero_le_one.trans s.hP
  have hPD : s.P ≤ s.slicedGeometryDimension := by
    dsimp [slicedGeometryDimension]
    have := Nat.cast_nonneg (α := ℝ) (layerTailDegree m + 1)
    linarith
  have hDg : s.D ≤ s.slicedGeometryDimension := s.hDP.trans hPD
  have hvg : 0 ≤ s.slicedGeometryRadiusLog := add_nonneg hP0 s.hPscale
  have hPvg : s.P ≤ s.slicedGeometryRadiusLog := le_add_of_nonneg_right s.hPscale
  have hScalevg : s.Pscale ≤ s.slicedGeometryRadiusLog := le_add_of_nonneg_left hP0
  have hcardA : (Fintype.card A : ℝ) ≤ s.D :=
    (Nat.cast_le.mpr (Fintype.card_le_of_injective selected s.hselected)).trans
      (allocatedIntegerAxes_card_le B (fun _ => Finset.univ : Fin m → Finset (Finset Empty)) s.hD)
  refine ⟨s.hP.trans hPD, hcardA.trans hDg, ?_, ?_, ?_, hvg,
    fun a => hR (selected a).1, ?_, ?_, ?_⟩
  · intro a
    exact (s.hD.layer_degree B (selected a).1).trans hDg
  · dsimp [slicedGeometryDimension]
    linarith
  · intro a
    have hblock : (Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩) : ℝ) ≤
        ∑ v : LayerSamplerAxis I n, (Fintype.card (B v) : ℝ) :=
      Finset.single_le_sum
        (f := fun v : LayerSamplerAxis I n => (Fintype.card (B v) : ℝ))
        (fun _ _ => Nat.cast_nonneg _)
        (Finset.mem_univ (⟨(selected a).1, Sum.inr (selected a).2⟩ : LayerSamplerAxis I n))
    exact (hblock.trans s.hblocks).trans hPD
  · intro a
    exact (s.hR1 a).trans (Real.one_le_exp_iff.mpr hvg)
  · intro a
    exact (s.hRinv a).trans (Real.exp_le_exp.mpr hScalevg)
  · intro a
    exact ((s.hD.coefficients (selected a).1).trans s.hDP).trans
      ((by linarith [Real.add_one_le_exp s.P] : s.P ≤ Real.exp s.P).trans
        (Real.exp_le_exp.mpr hPvg))

omit [DecidableEq X] [Fintype A] in
theorem sliced_ambient_coordinate_cutoff_bounds :
    let Lcoord := s.K * ∑ j, s.forward j * Fintype.card (J j)
    let Lcut := (Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound /
      (2 * s.radius)) * Lcoord
    (Lcoord : ℝ) ≤ Real.exp (s.PK + s.PF + s.D) ∧
    (Lcut : ℝ) ≤ Real.exp (s.PK + s.PF + 2 * s.D + normalizedSiteCutoffBound + 1) := by
  apply forecast_ambient_coordinate_cutoff_exp_bounds s.forward s.K s.radius
    s.hD.nonneg s.hPK s.hPF s.hdim s.haxes s.hforwardBound s.hKBound
  have h3 := s.hr3
  change (1 : ℝ) ≤ (s.radius : ℝ)
  linarith

omit [DecidableEq X] [Fintype A] in
theorem sliced_spatial_coordinate_bound :
    (max ⟨8 / τ, by have := s.hτ; positivity⟩ 1 : ℝ≥0) ≤
      ⟨Real.exp (s.Pτ + 8), Real.exp_nonneg _⟩ :=
  forecast_spatial_coordinate_exp_bound s.hτ s.hPτ s.hτinv

end ActualFixedSpatialForecastSetup
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedActualSlicedForecastSetup
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {A : Type} [Fintype A]
variable {Dmod : ℕ} {selected : A → Σ j : Fin m, Fin (n j)}
variable {τ δslice : ℝ}

variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod selected τ δslice)

theorem exists_actualFixedSpatialSlicedForecastNumerics_from_setup
    (δ : ℝ) (Hchild : ℕ) (kernelV Ptail p w vchild E : ℝ)
    (hδ : 0 < δ) (hk : 0 ≤ kernelV) (hPtail : 1 ≤ Ptail)
    (hprimitive : s.Pcap ≤ Ptail) (hp : 0 ≤ p) (hw : 0 ≤ w)
    (hvc : 0 ≤ vchild) (hE : 0 ≤ E)
    (hPp : Ptail ≤ Real.exp p)
    (hδw : δ⁻¹ ≤ Real.exp w) (hchild : (Hchild : ℝ) ≤ Real.exp vchild)
    (hR : ∀ j, 0 < R j) :
    let D := s.slicedGeometryDimension
    let v := s.slicedGeometryRadiusLog
    let Pspatial := s.Pτ + 8
    let Pcoord := s.PK + s.PF + s.D
    let Pcut := s.PK + s.PF + 2 * s.D + normalizedSiteCutoffBound + 1
    let Psm := forecastOriginalSmoothBudget m (s.P + (Fintype.card X + 1) * kernelV)
    let tailLog := slicedFixedUniformSiteLog m (p + slicedFixedZeroGeometryLog D v w 0 vchild) 0
    let Pin := D * tailLog
    let Pdec := (s.Pbad + s.Ppres) * ((Dmod + 2 : ℕ) : ℝ) * modularRankChargeFactor m
    let V := Pin + Pdec + (E + s.Pκ + Psm) + 3
    let Esite := E + s.Pκ + Psm + 1 + ((Dmod + 1 : ℕ) : ℝ) * V
    let pAll := p + V + slicedFixedZeroGeometryLog D v w V vchild
    let Q := slicedFixedUniformSiteLog m pAll (slicedFixedUniformAccuracyLog m D pAll Esite)
    let O := siteExponentialOutputLog 1 Q
    let Pnative := (V + D * O) + (Psm + D + O + 1 + Pspatial) + Pcoord + Pcut + 1
    let Pmass := Psm + ((Dmod + 1 : ℕ) : ℝ) * V + D * O + 1
    let Pcap := Psm + Pin + Pdec + 1
    ∃ nu : ActualFixedSpatialSlicedForecastNumerics s,
      nu.δ = δ ∧ nu.Hchild = Hchild ∧ nu.v = kernelV ∧ nu.Ptail = Ptail ∧ nu.E = E ∧
      nu.Pnative = Pnative ∧ nu.massLog = s.Pκ + Pmass ∧ nu.capLog = s.Pκ + Pcap ∧
      nu.Ctail = Real.exp tailLog ∧ (nu.T : ℝ) ≤ Real.exp V ∧
      0 ≤ nu.massLog ∧ 0 ≤ nu.capLog := by
  intro D v Pspatial Pcoord Pcut
  obtain ⟨hD, hcard, hdegree, htail, hblocks, hv, hRselected, hRv, hRi, hcoeff⟩ :=
    ActualFixedSpatialForecastSetup.sliced_primitive_geometry_bounds
      (B := B) (U := U) (b := b) (S := S) (X := X) (Eout := Eout) s hR
  have hPK := s.hPK
  have hPF := s.hPF
  have hD0 := s.hD.nonneg
  have hPτ := s.hPτ
  have hsp : 0 ≤ Pspatial := by dsimp [Pspatial]; positivity
  have hco : 0 ≤ Pcoord := by dsimp [Pcoord]; positivity
  have hcu : 0 ≤ Pcut := by dsimp [Pcut]; positivity
  have hspatial : max (8 / τ) 1 ≤ Real.exp Pspatial := by
    exact_mod_cast s.sliced_spatial_coordinate_bound
  obtain ⟨hcoord, hcut⟩ := s.sliced_ambient_coordinate_cutoff_bounds
  exact exists_actualFixedSpatialSlicedForecastNumerics_s2 s δ Hchild kernelV Ptail D p v w vchild E
    Pspatial Pcoord Pcut hδ hk hPtail hprimitive hD hp hv hw hvc hE hsp hco hcu
    hcard hPp hδw hchild hRselected hdegree htail hblocks hRv hRi hcoeff hspatial hcoord hcut

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedSlicedForecastComparisonLogs
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem preparedSlicedForecastTailCap_primitive_le (cost : ℝ) :
    preparedSlicedForecastPrimitiveCap ≤ preparedSlicedForecastTailCap cost :=
  le_max_left _ _

theorem preparedSlicedForecastTailCap_one_le (cost : ℝ) :
    1 ≤ preparedSlicedForecastTailCap cost :=
  preparedSlicedForecastPrimitiveCap_one_le.trans
    (preparedSlicedForecastTailCap_primitive_le cost)

theorem preparedSlicedForecastKernelLog_nonneg {cost : ℝ} (hcost : 0 ≤ cost) :
    0 ≤ preparedSlicedForecastKernelLog cost := by
  unfold preparedSlicedForecastKernelLog
  linarith

theorem preparedSlicedForecastDensity_pos (cost : ℝ) :
    0 < preparedSlicedForecastDensity cost := Real.exp_pos _

theorem preparedSlicedForecastDensity_inv (cost : ℝ) :
    (preparedSlicedForecastDensity cost)⁻¹ = Real.exp cost := by
  simp only [preparedSlicedForecastDensity, ← Real.exp_neg, neg_neg]

theorem preparedSlicedForecastTailCap_le_exp {cost : ℝ} (hcost : 0 ≤ cost) :
    preparedSlicedForecastTailCap cost ≤ Real.exp (preparedSlicedForecastTailLog cost) := by
  have hC := preparedSlicedForecastPrimitiveCap_one_le
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    norm_num at this ⊢
    exact this
  unfold preparedSlicedForecastTailCap preparedSlicedForecastTailLog
  refine max_le ?_ ?_
  · apply (le_trans (by linarith : preparedSlicedForecastPrimitiveCap ≤
      preparedSlicedForecastPrimitiveCap + 1)
      (Real.add_one_le_exp preparedSlicedForecastPrimitiveCap)).trans
    exact Real.exp_le_exp.mpr (by linarith)
  · calc
      2 * Real.exp cost ≤ Real.exp 1 * Real.exp cost :=
        mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
      _ = Real.exp (1 + cost) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (preparedSlicedForecastPrimitiveCap + cost + 1) :=
        Real.exp_le_exp.mpr (by linarith)

theorem preparedSlicedForecastChildSize_upper {childLog : ℝ} (hchildLog : 0 ≤ childLog) :
    (preparedSlicedForecastChildSize childLog : ℝ) ≤ Real.exp (childLog + 1) :=
  ceil_exp_le_exp_add_one hchildLog

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedConcreteSlicedForecastPrecision
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

private theorem and_rec_projection_p2 {p q : Prop} {α : Sort*}
    (f : p → q → α) (h : p ∧ q) : And.rec f h = f h.1 h.2 := by
  cases h
  rfl

variable {X₀ J₀ : Type} {m : ℕ} (L : RankPreparationFamily X₀ J₀ m) (Jalloc : ℕ)
variable (U : ∀ j : Fin m, Submodule ℝ ((fun j : Fin m => RankPreparationLayer.Coord (L j)) j → ℝ))
variable (b : ∀ j, Basis (Fin (preparedSamplerTransverse L j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous L j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ}
variable (S : LayerSamplerScale («J» := (fun j : Fin m => RankPreparationLayer.Coord (L j))) («G» := EnlargedPreparedCommonKernel m Jalloc)
  (EnlargedPreparedCommonSamplerBlock L Jalloc) U b R σ)
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (bW : ∀ j, Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice ((fun j : Fin m => RankPreparationLayer.Coord (L j)) j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

variable [∀ j, IsZLattice ℝ (latticeSection
  (standardEuclideanLattice (RankPreparationLayer.Coord (L j))) (euclideanSubspace (U j)))]
theorem preparedActualSlicedForecastSetup_scalar_values {M nX : ℕ}
    (hm : 0 < m) (hCoord : ∀ j, Fintype.card (L j).Coord ≤ M)
    {pRadius gainLog Qstride PF Pchart cost : ℝ} (Pdim : ℝ)
    (hpRadius : 0 ≤ pRadius) (hGain : 0 ≤ gainLog)
    (hQstride : 0 ≤ Qstride) (hPF : 0 ≤ PF) (hChart : 0 ≤ Pchart)
    (hcost : 0 ≤ cost)
    (hratio : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Real.exp Pchart)
    (hR : ∀ j, 0 < R j) (hRone : ∀ j, R j ≤ 1)
    (hRinv : ∀ j, (R j)⁻¹ ≤ Real.exp pRadius) (hσone : ∀ j, σ j ≤ 1)
    (forward : Fin m → ℝ≥0)
    (hforward : ∀ j : Fin m, ∀ w : EuclideanSpace ℝ (RankPreparationLayer.Coord (L j)), ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ forward j * ‖w‖)
    (hforwardBound : ∀ j, (forward j : ℝ) ≤ Real.exp PF)
    (radius : ℝ≥0) (T : Fin m → ℝ)
    (hT : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables (EnlargedPreparedCommonKernel m Jalloc) (PreparedSamplerContinuous L) (preparedSamplerTransverse L) (EnlargedPreparedCommonSamplerBlock L Jalloc)) (j.val + 1)) : ℝ) *
      (2 * 2 ^ (j.val + 1)) ≤ T j)
    (hradius : ∀ j : Fin m, (boundedBooleanJetRows (Fin 1) (j.val + 1)).card * T j ≤ (radius : ℝ))
    (inverse : Fin m → ℝ) (hinverse : ∀ j, 0 ≤ inverse j)
    (hchart : ∀ j (w : euclideanSubspace (U j) × (Fin (preparedSamplerTransverse L j) → ℝ)), ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm w‖ ≤ inverse j * ‖w‖)
    (hsourceBudget : ∀ j : Fin m,
      ((boundedBooleanJetRows (Fin 1) (j.val + 1)).card + 1 : ℝ) *
        (Fintype.card (Finset (Fin 1)) : ℝ) *
        (inverse j * (((Fintype.card ((PreparedSamplerContinuous L) j) : ℝ) + 1) * (2 * (radius : ℝ) * R j))) ≤ 1 / 4) :
    let s := preparedActualSlicedForecastSetup (nX := nX) L Jalloc U b o S bW hb hm hCoord Pdim
      hpRadius hGain hQstride hPF hChart hcost hratio hR hRone hRinv hσone
      forward hforward hforwardBound radius T hT hradius inverse hinverse hchart hsourceBudget
    s.P = preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost ∧
    s.Pscale = allocatedComparisonDimension m (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) + pRadius + 1 ∧
    s.Pbad = preparedSlicedForecastBadLog m nX Qstride gainLog ∧
    s.Ppres = cost + 1 ∧
    s.Pκ = preparedSlicedForecastJacobianLog m M nX pRadius gainLog Pchart ∧
    s.κ = forecastGeometricJacobian (X := Fin nX) («I» := (PreparedSamplerContinuous L)) U b R S.value
      (preparedForecastGridVolume L Jalloc U b S) (Real.exp (-(gainLog + (nX : ℝ) + 8))) ∧
    s.Pcap = max 1 (scalarCubePrimitiveEnvelope Empty scalarSourceTransitionBound 1 0 1) := by
  simp only [preparedActualSlicedForecastSetup, preparedActualForecastSetup,
    and_rec_projection_p2, ActualFixedSpatialForecastSetup.enlargeP,
    ActualFixedSpatialForecastSetup.withSliceWidth, preparedSlicedForecastJacobianLog]
  trivial

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedConcreteSlicedForecastModelLogs
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

private theorem and_rec_projection_p1 {p q : Prop} {α : Sort*}
    (f : p → q → α) (h : p ∧ q) : And.rec f h = f h.1 h.2 := by
  cases h
  rfl

variable {X₀ J₀ : Type} {m : ℕ} (L : RankPreparationFamily X₀ J₀ m) (Jalloc : ℕ)
variable (U : ∀ j : Fin m, Submodule ℝ ((fun j : Fin m => RankPreparationLayer.Coord (L j)) j → ℝ))
variable (b : ∀ j, Basis (Fin (preparedSamplerTransverse L j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous L j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ}
variable (S : LayerSamplerScale («J» := (fun j : Fin m => RankPreparationLayer.Coord (L j))) («G» := EnlargedPreparedCommonKernel m Jalloc)
  (EnlargedPreparedCommonSamplerBlock L Jalloc) U b R σ)
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (bW : ∀ j, Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice ((fun j : Fin m => RankPreparationLayer.Coord (L j)) j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

variable [∀ j, IsZLattice ℝ (latticeSection
  (standardEuclideanLattice (RankPreparationLayer.Coord (L j))) (euclideanSubspace (U j)))]
theorem preparedActualSlicedForecastSetup_scalar_values_extended {M nX : ℕ}
    (hm : 0 < m) (hCoord : ∀ j, Fintype.card (L j).Coord ≤ M)
    {pRadius gainLog Qstride PF Pchart cost : ℝ} (Pdim : ℝ)
    (hpRadius : 0 ≤ pRadius) (hGain : 0 ≤ gainLog)
    (hQstride : 0 ≤ Qstride) (hPF : 0 ≤ PF) (hChart : 0 ≤ Pchart)
    (hcost : 0 ≤ cost)
    (hratio : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Real.exp Pchart)
    (hR : ∀ j, 0 < R j) (hRone : ∀ j, R j ≤ 1)
    (hRinv : ∀ j, (R j)⁻¹ ≤ Real.exp pRadius) (hσone : ∀ j, σ j ≤ 1)
    (forward : Fin m → ℝ≥0)
    (hforward : ∀ j : Fin m, ∀ w : EuclideanSpace ℝ (RankPreparationLayer.Coord (L j)), ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ forward j * ‖w‖)
    (hforwardBound : ∀ j, (forward j : ℝ) ≤ Real.exp PF)
    (radius : ℝ≥0) (T : Fin m → ℝ)
    (hT : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables (EnlargedPreparedCommonKernel m Jalloc) (PreparedSamplerContinuous L) (preparedSamplerTransverse L) (EnlargedPreparedCommonSamplerBlock L Jalloc)) (j.val + 1)) : ℝ) *
      (2 * 2 ^ (j.val + 1)) ≤ T j)
    (hradius : ∀ j : Fin m, (boundedBooleanJetRows (Fin 1) (j.val + 1)).card * T j ≤ (radius : ℝ))
    (inverse : Fin m → ℝ) (hinverse : ∀ j, 0 ≤ inverse j)
    (hchart : ∀ j (w : euclideanSubspace (U j) × (Fin (preparedSamplerTransverse L j) → ℝ)), ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm w‖ ≤ inverse j * ‖w‖)
    (hsourceBudget : ∀ j : Fin m,
      ((boundedBooleanJetRows (Fin 1) (j.val + 1)).card + 1 : ℝ) *
        (Fintype.card (Finset (Fin 1)) : ℝ) *
        (inverse j * (((Fintype.card ((PreparedSamplerContinuous L) j) : ℝ) + 1) * (2 * (radius : ℝ) * R j))) ≤ 1 / 4) :
    let s := preparedActualSlicedForecastSetup (nX := nX) L Jalloc U b o S bW hb hm hCoord Pdim
      hpRadius hGain hQstride hPF hChart hcost hratio hR hRone hRinv hσone
      forward hforward hforwardBound radius T hT hradius inverse hinverse hchart hsourceBudget
    s.Pτ = gainLog + nX + 8 ∧ s.PK = pRadius ∧ s.PF = PF ∧
      s.D = allocatedComparisonDimension m (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) := by
  simp only [preparedActualSlicedForecastSetup, preparedActualForecastSetup,
    and_rec_projection_p1, ActualFixedSpatialForecastSetup.enlargeP,
    ActualFixedSpatialForecastSetup.withSliceWidth]
  trivial

theorem preparedConcreteSlicedForecastEarlyLogs {M nX : ℕ}
    (hm : 0 < m) (hCoord : ∀ j, Fintype.card (L j).Coord ≤ M)
    {pRadius gainLog Qstride PF Pchart cost : ℝ} (Pdim : ℝ)
    (hpRadius : 0 ≤ pRadius) (hGain : 0 ≤ gainLog)
    (hQstride : 0 ≤ Qstride) (hPF : 0 ≤ PF) (hChart : 0 ≤ Pchart)
    (hcost : 0 ≤ cost)
    (hratio : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Real.exp Pchart)
    (hR : ∀ j, 0 < R j) (hRone : ∀ j, R j ≤ 1)
    (hRinv : ∀ j, (R j)⁻¹ ≤ Real.exp pRadius) (hσone : ∀ j, σ j ≤ 1)
    (forward : Fin m → ℝ≥0)
    (hforward : ∀ j : Fin m, ∀ w : EuclideanSpace ℝ (RankPreparationLayer.Coord (L j)), ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ forward j * ‖w‖)
    (hforwardBound : ∀ j, (forward j : ℝ) ≤ Real.exp PF)
    (radius : ℝ≥0) (T : Fin m → ℝ)
    (hT : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables (EnlargedPreparedCommonKernel m Jalloc) (PreparedSamplerContinuous L) (preparedSamplerTransverse L) (EnlargedPreparedCommonSamplerBlock L Jalloc)) (j.val + 1)) : ℝ) *
      (2 * 2 ^ (j.val + 1)) ≤ T j)
    (hradius : ∀ j : Fin m, (boundedBooleanJetRows (Fin 1) (j.val + 1)).card * T j ≤ (radius : ℝ))
    (inverse : Fin m → ℝ) (hinverse : ∀ j, 0 ≤ inverse j)
    (hchart : ∀ j (w : euclideanSubspace (U j) × (Fin (preparedSamplerTransverse L j) → ℝ)), ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm w‖ ≤ inverse j * ‖w‖)
    (hsourceBudget : ∀ j : Fin m,
      ((boundedBooleanJetRows (Fin 1) (j.val + 1)).card + 1 : ℝ) *
        (Fintype.card (Finset (Fin 1)) : ℝ) *
        (inverse j * (((Fintype.card ((PreparedSamplerContinuous L) j) : ℝ) + 1) * (2 * (radius : ℝ) * R j))) ≤ 1 / 4)
    (childLog E : ℝ) (hchildLog : 0 ≤ childLog) (hE : 0 ≤ E) :
    let s := preparedActualSlicedForecastSetup (nX := nX) L Jalloc U b o S bW hb hm hCoord Pdim
      hpRadius hGain hQstride hPF hChart hcost hratio hR hRone hRinv hσone
      forward hforward hforwardBound radius T hT hradius inverse hinverse hchart hsourceBudget
    ∃ q : ActualFixedSpatialSlicedForecastNumerics s,
      q.δ = preparedSlicedForecastDensity cost ∧
      q.Hchild = preparedSlicedForecastChildSize childLog ∧ q.v = cost + 1 ∧
      q.Ptail = preparedSlicedForecastTailCap cost ∧ q.E = E ∧
      q.Pnative = preparedConcreteSlicedForecastNativeLog m M nX Jalloc
        Pdim cost pRadius gainLog Qstride PF Pchart childLog E ∧
      q.massLog = preparedConcreteSlicedForecastMassLog m M nX Jalloc
        Pdim cost pRadius gainLog Qstride Pchart childLog E ∧
      q.capLog = preparedConcreteSlicedForecastCapLog m M nX Jalloc
        Pdim cost pRadius gainLog Qstride Pchart childLog ∧
      q.Ctail = Real.exp (preparedConcreteSlicedForecastTailSiteLog m M nX Jalloc
        Pdim cost pRadius childLog) ∧
      (q.T : ℝ) ≤ Real.exp (preparedConcreteSlicedForecastPeriodLog m M nX Jalloc
        Pdim cost pRadius gainLog Qstride Pchart childLog E) ∧
      0 ≤ q.massLog ∧ 0 ≤ q.capLog ∧ 0 ≤ q.Pnative := by
  intro s
  obtain ⟨hP, hscale, hbad, hpres, hκ, _, hprimitiveEq⟩ :=
    preparedActualSlicedForecastSetup_scalar_values (nX := nX) L Jalloc U b o S bW hb hm hCoord Pdim
      hpRadius hGain hQstride hPF hChart hcost hratio hR hRone hRinv hσone
      forward hforward hforwardBound radius T hT hradius inverse hinverse hchart hsourceBudget
  obtain ⟨hτ, hPK, hPF', hD⟩ :=
    preparedActualSlicedForecastSetup_scalar_values_extended (nX := nX) L Jalloc U b o S bW hb hm hCoord Pdim
      hpRadius hGain hQstride hPF hChart hcost hratio hR hRone hRinv hσone
      forward hforward hforwardBound radius T hT hradius inverse hinverse hchart hsourceBudget
  change s.P = _ at hP
  change s.Pscale = _ at hscale
  change s.Pbad = _ at hbad
  change s.Ppres = _ at hpres
  change s.Pκ = _ at hκ
  change s.Pcap = _ at hprimitiveEq
  change s.Pτ = _ at hτ
  change s.PK = _ at hPK
  change s.PF = _ at hPF'
  change s.D = _ at hD
  have hprimitive : s.Pcap ≤ preparedSlicedForecastTailCap cost :=
    hprimitiveEq.trans_le (preparedSlicedForecastTailCap_primitive_le cost)
  obtain ⟨q, hq⟩ := exists_actualFixedSpatialSlicedForecastNumerics_from_setup s
    (preparedSlicedForecastDensity cost) (preparedSlicedForecastChildSize childLog)
    (cost + 1) (preparedSlicedForecastTailCap cost) (preparedSlicedForecastTailLog cost)
    cost (childLog + 1) E
    (preparedSlicedForecastDensity_pos cost)
    (preparedSlicedForecastKernelLog_nonneg hcost)
    (preparedSlicedForecastTailCap_one_le cost) hprimitive
    (preparedSlicedForecastTailLog_nonneg hcost) hcost (by linarith) hE
    (preparedSlicedForecastTailCap_le_exp hcost)
    (preparedSlicedForecastDensity_inv cost).le
    (preparedSlicedForecastChildSize_upper hchildLog) hR
  refine ⟨q, ?_⟩
  have hqall := And.intro hq q.hPnative
  simpa only [ActualFixedSpatialForecastSetup.slicedGeometryDimension,
    ActualFixedSpatialForecastSetup.slicedGeometryRadiusLog,
    hP, hscale, hbad, hpres, hκ, hτ, hPK, hPF', hD, Fintype.card_fin,
    preparedConcreteSlicedForecastNativeLog, preparedConcreteSlicedForecastMassLog,
    preparedConcreteSlicedForecastCapLog, preparedConcreteSlicedForecastTailSiteLog,
    preparedConcreteSlicedForecastOutputLog, preparedConcreteSlicedForecastPeriodLog,
    preparedSlicedForecastCapLog, actualSlicedForecastModelCapLog,
    actualSlicedForecastModelPeriodLog, and_assoc] using hqall

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedSourceSlicedForecastNumerics
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {X₀ J₀ : Type} {m : ℕ} (L : RankPreparationFamily X₀ J₀ m) (Jalloc : ℕ)
variable (U : ∀ j : Fin m, Submodule ℝ ((fun j : Fin m => RankPreparationLayer.Coord (L j)) j → ℝ))
variable (b : ∀ j, Basis (Fin (preparedSamplerTransverse L j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous L j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ}
variable (S : LayerSamplerScale («J» := (fun j : Fin m => RankPreparationLayer.Coord (L j))) («G» := EnlargedPreparedCommonKernel m Jalloc)
  (EnlargedPreparedCommonSamplerBlock L Jalloc) U b R σ)
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (bW : ∀ j, Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice ((fun j : Fin m => RankPreparationLayer.Coord (L j)) j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

variable [∀ j, IsZLattice ℝ (latticeSection
  (standardEuclideanLattice (RankPreparationLayer.Coord (L j))) (euclideanSubspace (U j)))]
theorem exists_preparedSourceSlicedForecastNumerics_s2_oai {M nX : ℕ}
    (hm : 0 < m) (hCoord : ∀ j, Fintype.card (L j).Coord ≤ M)
    {pRadius gainLog Qstride PF Pchart cost : ℝ} (Pdim : ℝ)
    (hpRadius : 0 ≤ pRadius) (hGain : 0 ≤ gainLog)
    (hQstride : 0 ≤ Qstride) (hPF : 0 ≤ PF) (hChart : 0 ≤ Pchart)
    (hcost : 0 ≤ cost)
    (hratio : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Real.exp Pchart)
    (hR : ∀ j, 0 < R j) (hRone : ∀ j, R j ≤ 1)
    (hRinv : ∀ j, (R j)⁻¹ ≤ Real.exp pRadius) (hσone : ∀ j, σ j ≤ 1)
    (forward : Fin m → ℝ≥0)
    (hforward : ∀ j : Fin m, ∀ w : EuclideanSpace ℝ (RankPreparationLayer.Coord (L j)), ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ forward j * ‖w‖)
    (hforwardBound : ∀ j, (forward j : ℝ) ≤ Real.exp PF)
    (inverse : Fin m → ℝ) (hinverse : ∀ j, 0 ≤ inverse j)
    (hchart : ∀ j (w : euclideanSubspace (U j) × (Fin (preparedSamplerTransverse L j) → ℝ)),
      ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm w‖ ≤ inverse j * ‖w‖)
    {Cdetect : ℕ} {Bstruct Pscale Dgeometry target Pk Prho pDetect aDetect detectionGain : ℝ}
    (hInverseBound : ∀ j, inverse j ≤ Real.exp Bstruct)
    (hgeometry : PreparedUniformDegreeGeometryAt
      (EnlargedPreparedCommonSamplerBlock L Jalloc) U b S 0 Cdetect nX
      Bstruct Pscale Dgeometry target Pk Prho Qstride pDetect pRadius aDetect detectionGain)
    (childLog E : ℝ) (hchildLog : 0 ≤ childLog) (hE : 0 ≤ E) :
    let s := preparedActualSlicedForecastSetupOfSourceGeometry (nX := nX)
      L Jalloc U b o S bW hb hm hCoord Pdim hpRadius hGain hQstride hPF hChart
      hcost hratio hR hRone hRinv hσone forward hforward hforwardBound
      inverse hinverse hchart hInverseBound hgeometry
    ∃ q : ActualFixedSpatialSlicedForecastNumerics s,
      q.δ = preparedSlicedForecastDensity cost ∧
      q.Hchild = preparedSlicedForecastChildSize childLog ∧ q.v = cost + 1 ∧
      q.Ptail = preparedSlicedForecastTailCap cost ∧ q.E = E ∧
      q.Pnative = preparedConcreteSlicedForecastNativeLog m M nX Jalloc
        Pdim cost pRadius gainLog Qstride PF Pchart childLog E ∧
      q.massLog = preparedConcreteSlicedForecastMassLog m M nX Jalloc
        Pdim cost pRadius gainLog Qstride Pchart childLog E ∧
      q.capLog = preparedConcreteSlicedForecastCapLog m M nX Jalloc
        Pdim cost pRadius gainLog Qstride Pchart childLog ∧
      q.Ctail = Real.exp (preparedConcreteSlicedForecastTailSiteLog m M nX Jalloc
        Pdim cost pRadius childLog) ∧
      (q.T : ℝ) ≤ Real.exp (preparedConcreteSlicedForecastPeriodLog m M nX Jalloc
        Pdim cost pRadius gainLog Qstride Pchart childLog E) ∧
      0 ≤ q.massLog ∧ 0 ≤ q.capLog ∧ 0 ≤ q.Pnative := by
  let geometry := Classical.choice hgeometry.1
  exact preparedConcreteSlicedForecastEarlyLogs (nX := nX) L Jalloc U b o S bW hb hm hCoord Pdim
    hpRadius hGain hQstride hPF hChart hcost hratio hR hRone hRinv hσone
    forward hforward hforwardBound geometry.siteRadius geometry.T
    (fun j => by
      have h := geometry.hsource j
      norm_num only [Fintype.card_fin, Nat.cast_one, pow_one] at h
      exact h) geometry.hradius
    inverse hinverse hchart (fun j => by
      simpa only [mul_assoc] using (geometry.hbudgets inverse hinverse hInverseBound).2.2 j)
    childLog E hchildLog hE

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.exists_preparedSourceSlicedForecastNumerics_s2_oai := @OAI.Erdos3.VectorPolynomial.exists_preparedSourceSlicedForecastNumerics_s2_oai
