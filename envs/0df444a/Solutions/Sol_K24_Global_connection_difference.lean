-- Prove2me | solution 1 for K24.Global.connection_difference
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T18:35:14.550022+00:00
-- url     : https://prove2.me/submissions/561537a8-fa52-46e7-b7d1-088934019a1c

import Definitions.Def_K24GlobalStatement

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

noncomputable section
open scoped BigOperators
open Matrix

namespace K24.Global.ConnectionProof

abbrev Jet := Fin 4 → Fin 4 → Fin 4 → ℝ

def koszul (d : Jet) (i j l : Fin 4) : ℝ := d i j l + d j i l - d l i j

def gamma (a : Mat4) (d : Jet) (k i j : Fin 4) : ℝ :=
  (1 / 2 : ℝ) * ∑ l, a⁻¹ k l * koszul d i j l

def nabla (G : Jet) (h : Mat4) (d : Jet) (i j l : Fin 4) : ℝ :=
  d i j l - (∑ p, G p i j * h p l) - (∑ p, G p i l * h j p)

theorem gamma_symmetric (a : Mat4) (d : Jet)
    (hd : ∀ i j l, d i j l = d i l j) (k i j : Fin 4) :
    gamma a d k i j = gamma a d k j i := by
  unfold gamma koszul
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  rw [hd l i j]
  ring

theorem koszul_nabla (G : Jet) (h : Mat4) (d : Jet)
    (hG : ∀ k i j, G k i j = G k j i)
    (hh : ∀ i j, h i j = h j i) (i j l : Fin 4) :
    nabla G h d i j l + nabla G h d j i l - nabla G h d l i j =
      koszul d i j l - 2 * ∑ p, G p i j * h p l := by
  unfold nabla koszul
  have h₁ : (∑ p, G p j i * h p l) = ∑ p, G p i j * h p l := by
    apply Finset.sum_congr rfl
    intro p _
    rw [hG p j i]
  have h₂ : (∑ p, G p l i * h p j) = ∑ p, G p i l * h j p := by
    apply Finset.sum_congr rfl
    intro p _
    rw [hG p l i, hh p j]
  have h₃ : (∑ p, G p l j * h i p) = ∑ p, G p j l * h i p := by
    apply Finset.sum_congr rfl
    intro p _
    rw [hG p l j]
  rw [h₁, h₂, h₃]
  ring

theorem inverse_contraction (a : Mat4) (ha : IsUnit a.det)
    (hs : ∀ i j, a i j = a j i) (v : Fin 4 → ℝ) (k : Fin 4) :
    (∑ l, a⁻¹ k l * ∑ p, v p * a p l) = v k := by
  have hinner : (fun l => ∑ p, v p * a p l) = a *ᵥ v := by
    funext l
    change (∑ p, v p * a p l) = ∑ p, a l p * v p
    apply Finset.sum_congr rfl
    intro p _
    rw [hs p l]
    ring
  change (a⁻¹ *ᵥ (fun l => ∑ p, v p * a p l)) k = v k
  rw [hinner, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul a ha, Matrix.one_mulVec]

theorem lower_gamma (a : Mat4) (d : Jet) (ha : IsUnit a.det)
    (hs : ∀ i j, a i j = a j i) (i j l : Fin 4) :
    2 * (∑ p, gamma a d p i j * a p l) = koszul d i j l := by
  have hinner : (∑ p, gamma a d p i j * a p l) =
      (1 / 2 : ℝ) * (a *ᵥ (a⁻¹ *ᵥ (fun r => koszul d i j r))) l := by
    change (∑ p, gamma a d p i j * a p l) =
      (1 / 2 : ℝ) * ∑ p, a l p * ∑ r, a⁻¹ p r * koszul d i j r
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    rw [hs p l]
    unfold gamma
    ring
  rw [hinner, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv a ha, Matrix.one_mulVec]
  ring

theorem connection_difference_algebra (a b : Mat4) (da db : Jet)
    (ha : IsUnit a.det) (hb : IsUnit b.det)
    (has : ∀ i j, a i j = a j i) (hbs : ∀ i j, b i j = b j i)
    (hdb : ∀ i j l, db i j l = db i l j) (k i j : Fin 4) :
    gamma a da k i j - gamma b db k i j =
      (1 / 2 : ℝ) * ∑ l, a⁻¹ k l *
        (nabla (gamma b db) (a - b) (da - db) i j l +
         nabla (gamma b db) (a - b) (da - db) j i l -
         nabla (gamma b db) (a - b) (da - db) l i j) := by
  have hs : ∀ i j, (a - b) i j = (a - b) j i := by
    intro i j
    simp only [Matrix.sub_apply, has i j, hbs i j]
  simp_rw [koszul_nabla _ _ _ (gamma_symmetric b db hdb) hs]
  have hl (l : Fin 4) :
      koszul (da - db) i j l - 2 * ∑ p, gamma b db p i j * (a - b) p l =
        koszul da i j l - 2 * ∑ p, gamma b db p i j * a p l := by
    simp only [koszul, Pi.sub_apply, Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib]
    have h := lower_gamma b db hb hbs i j l
    unfold koszul at h
    linarith
  simp_rw [hl, mul_sub, Finset.sum_sub_distrib]
  have hc : (∑ l, a⁻¹ k l * (2 * ∑ p, gamma b db p i j * a p l)) =
      2 * gamma b db k i j := by
    rw [← inverse_contraction a ha has (fun p => gamma b db p i j) k,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [hc]
  unfold gamma
  ring

end K24.Global.ConnectionProof


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise
open Matrix

namespace K24.Global

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

theorem cov2InChart_sub (g h : RawCov2 M) (c : M) (x : FourSpace) :
    cov2InChart (g - h) c x = cov2InChart g c x - cov2InChart h c x := by
  ext i j
  simp [cov2InChart, Matrix.sub_apply]

theorem cov2InChart_symmetric (g : RawCov2 M) (hg : IsSymmetricCov2 g)
    (c : M) (x : FourSpace) (i j : Fin 4) :
    cov2InChart g c x i j = cov2InChart g c x j i := by
  exact hg _ _ _

theorem cov2InChart_isUnit_det [IsManifold I4 ∞ M] (g : RawCov2 M)
    (hg : IsMetric g) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) :
    IsUnit (cov2InChart g c x).det := by
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.PosDef.isUnit
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    simpa only [Matrix.conjTranspose_apply, star_trivial] using
      cov2InChart_symmetric g hg.1 c x j i
  · intro v hv
    let w : FourSpace := ∑ i, v i • basisVector i
    have hw : w ≠ 0 := by
      intro hw
      apply hv
      funext i
      have h := congrArg (fun q : FourSpace => q i) hw
      simpa [w, basisVector, Pi.single_apply] using h
    let e := chartAt FourSpace c
    let di := mfderiv I4 I4 e.symm x
    have hinj : Function.Injective di := by
      apply Function.LeftInverse.injective (g := mfderiv I4 I4 e (e.symm x))
      intro v
      exact congrArg (fun A => A v) ((mdifferentiable_chart (I := I4) c).comp_symm_deriv hx)
    have hdi : di w ≠ 0 := by
      intro h
      exact hw (hinj (h.trans (map_zero di).symm))
    have hpos := hg.2 (e.symm x) (di w) hdi
    have heq : star v ⬝ᵥ (cov2InChart g c x *ᵥ v) =
        g (e.symm x) (di w) (di w) := by
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial,
        cov2InChart, w, map_sum, map_smul, _root_.sum_apply,
        _root_.smul_apply, smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hg.1 (e.symm x) (di (basisVector j)) (di (basisVector i))]
      ring
    rw [heq]
    exact hpos

theorem connection_difference_of_differentiableAt
    [IsManifold I4 ∞ M] (ghat z : RawCov2 M)
    (hghat : IsMetric ghat) (hz : IsMetric z)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target)
    (hDghat : DifferentiableAt ℝ (cov2InChart ghat c) x)
    (hDz : DifferentiableAt ℝ (cov2InChart z c) x) (k i j : Fin 4) :
    connectionDifferenceInChart ghat z c x k i j =
      connectionDifferenceExpansion ghat z c x k i j := by
  let da : ConnectionProof.Jet := fun i j l =>
    coordDeriv (fun y => cov2InChart ghat c y j l) i x
  let db : ConnectionProof.Jet := fun i j l =>
    coordDeriv (fun y => cov2InChart z c y j l) i x
  have hdb : ∀ i j l, db i j l = db i l j := by
    intro i j l
    have heq : (fun y => cov2InChart z c y j l) =
        (fun y => cov2InChart z c y l j) := by
      funext y
      exact cov2InChart_symmetric z hz.1 c y j l
    change coordDeriv _ i x = coordDeriv _ i x
    rw [heq]
  have hsub (i j l : Fin 4) :
      coordDeriv (fun y => cov2InChart (ghat - z) c y j l) i x =
        (da - db) i j l := by
    have ha := (differentiableAt_pi.mp (differentiableAt_pi.mp hDghat j)) l
    have hb := (differentiableAt_pi.mp (differentiableAt_pi.mp hDz j)) l
    simp only [cov2InChart_sub, Matrix.sub_apply]
    change fderiv ℝ ((fun y => cov2InChart ghat c y j l) -
      (fun y => cov2InChart z c y j l)) x (basisVector i) = _
    rw [fderiv_sub ha hb]
    rfl
  have h := ConnectionProof.connection_difference_algebra
    (cov2InChart ghat c x) (cov2InChart z c x) da db
    (cov2InChart_isUnit_det ghat hghat c x hx)
    (cov2InChart_isUnit_det z hz c x hx)
    (cov2InChart_symmetric ghat hghat.1 c x)
    (cov2InChart_symmetric z hz.1 c x) hdb k i j
  unfold connectionDifferenceInChart connectionDifferenceExpansion
  simp only [nablaTensorInChart, hsub]
  simpa only [christoffelInChart, inverseMetricInChart,
    cov2InChart_sub, ConnectionProof.gamma, ConnectionProof.koszul,
    ConnectionProof.nabla, da, db] using h

theorem connection_difference_of_cov2ContDiff
    [IsManifold I4 ∞ M] (ghat z : RawCov2 M)
    (hghat : IsMetric ghat) (hz : IsMetric z)
    (hDghat : Cov2ContDiff 1 ghat) (hDz : Cov2ContDiff 1 z)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target)
    (k i j : Fin 4) :
    connectionDifferenceInChart ghat z c x k i j =
      connectionDifferenceExpansion ghat z c x k i j := by
  apply connection_difference_of_differentiableAt ghat z hghat hz c x hx
  · exact ((hDghat c).differentiableOn (by simp) x hx).differentiableAt
      ((chartAt FourSpace c).open_target.mem_nhds hx)
  · exact ((hDz c).differentiableOn (by simp) x hx).differentiableAt
      ((chartAt FourSpace c).open_target.mem_nhds hx)

theorem connection_difference_of_sobolev_admissible
    [IsManifold I4 ∞ M] (C : BoundedLocalCover M) (L : SobolevLocalizers C)
    (s : ℝ) (b : SobolevMetricNumerics) (ghat z : RawCov2 M)
    (hghat : MetricSobolevAdmissible C L s b ghat)
    (hz : MetricSobolevAdmissible C L s b z)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target)
    (k i j : Fin 4) :
    connectionDifferenceInChart ghat z c x k i j =
      connectionDifferenceExpansion ghat z c x k i j := by
  apply connection_difference_of_cov2ContDiff ghat z hghat.metric hz.metric
  · intro c
    exact (hghat.representative c).of_le (by norm_num)
  · intro c
    exact (hz.representative c).of_le (by norm_num)
  · exact hx

universe u

theorem _root_.solution :
    ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M]
      [IsManifold I4 ∞ M],
      ∀ (ghat z : RawCov2 M), IsMetric ghat → IsMetric z →
        Cov2ContDiff 1 ghat → Cov2ContDiff 1 z →
        ∀ (c : M) (x : FourSpace), x ∈ (chartAt FourSpace c).target →
          ∀ k i j : Fin 4, connectionDifferenceInChart ghat z c x k i j =
            connectionDifferenceExpansion ghat z c x k i j := by
  intro M _ _ _ ghat z hghat hz hDghat hDz c x hx k i j
  exact connection_difference_of_cov2ContDiff ghat z hghat hz hDghat hDz c x hx k i j

end K24.Global
