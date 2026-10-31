-- Prove2me | solution 1 for OAI.AffineBernstein.affineEpigraph_product_area_chart
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T09:53:35.581318+00:00
-- url     : https://prove2.me/submissions/afc12306-d9d7-44f9-9925-6871a65de0e9

import Mathlib
import Definitions.Def_AffineBernstein
import Definitions.Def_OAIQ22Ab000
import Theorems.Thm_OAI_AffineBernstein_affineEpigraph_flat_chart_global_area_lintegral

section
-- module Solutions.OAIQ22_AB.AffineBernstein_FlatProductCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {S E F : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma flatProductEmbedding_injective (f : WithLp 2 (F × ℝ) ≃ₗᵢ[ℝ] E) :
    Function.Injective (flatProductEmbedding (S:=S) f) := by
  intro q r h
  have h₁ := congrArg Prod.fst h
  have h₂ := f.injective (congrArg Prod.snd h)
  exact Prod.ext h₁ (congrArg (fun z : WithLp 2 (F × ℝ) => (WithLp.ofLp z).1) h₂)

lemma flatProductEmbedding_vertical (bF : OrthonormalBasis κ ℝ F)
    (f : WithLp 2 (F × ℝ) ≃ₗᵢ[ℝ] E) (q : S × F) :
    inner ℝ (flatProductEmbedding f q).2 (flatProductFiberBasis bF f (Sum.inr ())) = 0 := by
  rw [flatProductEmbedding_apply,flatProductFiberBasis_last,f.inner_map_map]
  simp [WithLp.prod_inner_apply]

lemma flatProductCoordinates_basis {n : ℕ} (bS : OrthonormalBasis ι ℝ S)
    (bF : OrthonormalBasis κ ℝ F) (e : Fin n ≃ ι ⊕ κ) (i : Fin n) :
    flatProductCoordinates bS bF e (coordinateVector n i) =
      Sum.elim (fun j => (bS j,(0:F))) (fun j => ((0:S),bF j)) (e i) := by
  have h := ((bS.prod bF).reindex e.symm).repr_symm_single i
  change (WithLp.ofLp (((bS.prod bF).reindex e.symm).repr.symm (EuclideanSpace.single i 1))) = _
  rw [h,OrthonormalBasis.reindex_apply]
  simp only [Equiv.symm_symm]
  rcases e i with j | j <;> simp [OrthonormalBasis.prod_apply]

lemma flatProductEmbedding_affine (f : WithLp 2 (F × ℝ) ≃ₗᵢ[ℝ] E) (q : S × F) :
    ((0:S),f (WithLp.toLp 2 (0,(1:ℝ)))) + flatProductEmbedding f q =
      (q.1,f (WithLp.toLp 2 (q.2,(1:ℝ)))) := by
  rw [flatProductEmbedding_apply]
  apply Prod.ext
  · simp
  · change f (WithLp.toLp 2 (0,(1:ℝ))) + f (WithLp.toLp 2 (q.2,0)) = _
    rw [← map_add]
    congr 1
    change WithLp.toLp 2 ((0:F)+q.2,(1:ℝ)+0) = _
    simp

lemma flatProductCoordinates_measurePreserving [FiniteDimensional ℝ S] [FiniteDimensional ℝ F]
    [MeasurableSpace S] [BorelSpace S] [MeasurableSpace F] [BorelSpace F]
    {n : ℕ} (bS : OrthonormalBasis ι ℝ S) (bF : OrthonormalBasis κ ℝ F)
    (e : Fin n ≃ ι ⊕ κ) : MeasurePreserving (flatProductCoordinates bS bF e) := by
  exact (WithLp.volume_preserving_ofLp S F).comp
    (((bS.prod bF).reindex e.symm).repr.symm.measurePreserving)

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ProductAreaChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section ProductAreaChart
variable {S E F : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S]
  [FiniteDimensional ℝ S] [MeasurableSpace S] [BorelSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Actual graph-area change of variables in a full flat projective chart,
expressed in the true product Haar measure on base times angular plane. -/
theorem affineEpigraph_product_area_chart_oai {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set S} (hD : IsOpen D)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0:E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (bS : OrthonormalBasis ι ℝ S) (bF : OrthonormalBasis κ ℝ F)
    (f : WithLp 2 (F × ℝ) ≃ₗᵢ[ℝ] E) (e : Fin n ≃ ι ⊕ κ) :
    let Z := flatProductCoordinates bS bF e
    let bE := flatProductFiberBasis bF f
    let eA := (Equiv.sumCongr e (Equiv.refl Unit)).trans (Equiv.sumAssoc ι κ Unit)
    let b := (bS.toBasis.prod bE.toBasis).reindex eA.symm
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    ∃ φ : OpenPartialHomeomorph (Space n) (Space n),
      φ.source = {x | (Z x).1 ∈ D} ∧ φ.target ⊆ Ω ∧
      (∀ x ∈ φ.source, a+L ((Z x).1,
        gaussPoint {y | ((Z x).1,y) ∈ affineEpigraphPullback Ω u a L}
          (f (WithLp.toLp 2 ((Z x).2,(1:ℝ))))) = (φ x,u (φ x))) ∧
      ∀ {Q : Set S}, MeasurableSet Q → Q ⊆ D →
        ENNReal.ofReal (Real.rpow |b.det ((graphAmbientBasis n).map L.symm.toLinearEquiv)|
          ((n:ℝ)/((n:ℝ)+2))) *
          (∫⁻ y in φ '' (Z ⁻¹' (Q ×ˢ Set.univ)), ENNReal.ofReal (affineAreaDensity u y)) =
        (∫⁻ q : S × F, ENNReal.ofReal (tubeAreaDensity
          (tubeBaseMatrix H (q.1,f (WithLp.toLp 2 (q.2,(1:ℝ)))) bS.toBasis)
          (tubeRadiusMatrix H (q.1,f (WithLp.toLp 2 (q.2,(1:ℝ)))) bE)
          (1/((Fintype.card ι:ℝ)+Fintype.card κ+2))) ∂(volume.restrict Q).prod volume) := by
  let Z := flatProductCoordinates bS bF e
  let bE := flatProductFiberBasis bF f
  let J := (flatProductEmbedding (S:=S) f).comp Z.toContinuousLinearMap
  let q₀ : S × E := (0,f (WithLp.toLp 2 (0,(1:ℝ))))
  have hq (x : Space n) : q₀+J x = ((Z x).1,f (WithLp.toLp 2 ((Z x).2,(1:ℝ)))) :=
    flatProductEmbedding_affine f (Z x)
  have hd : inner ℝ q₀.2 (bE (Sum.inr ())) = 1 := by
    simp only [q₀,bE,flatProductFiberBasis_last,f.inner_map_map]
    simp
  have hJ : Function.Injective J := (flatProductEmbedding_injective f).comp Z.injective
  have hJvert (x : Space n) : inner ℝ (J x).2 (bE (Sum.inr ())) = 0 :=
    flatProductEmbedding_vertical bF f (Z x)
  have hJe (i : Fin n) : J (coordinateVector n i) = tubeTangent bS.toBasis bE (e i) := by
    change flatProductEmbedding f (Z (coordinateVector n i)) = _
    rw [flatProductCoordinates_basis]
    rcases e i with j | j <;> simp [tubeTangent,bE]
  obtain ⟨φ,hsource,ht,hφ,hψ,heφ,harea⟩ := affineEpigraph_flat_chart_global_area_lintegral
    hΩ hcv hu hp a L hD hK hzero q₀ bS.toBasis bE hd J hJ hJvert e hJe
  dsimp only
  refine ⟨φ,?_,ht,?_,?_⟩
  · simpa only [hq] using hsource
  · intro x hx
    simpa only [supportParam,hq] using heφ x hx
  · intro Q hQ hQD
    let T : Set (S × F) := Q ×ˢ univ
    have hT : MeasurableSet T := hQ.prod MeasurableSet.univ
    have hZT : MeasurableSet (Z ⁻¹' T) := hT.preimage Z.continuous.measurable
    have hZsource : Z ⁻¹' T ⊆ φ.source := by
      intro x hx
      rw [hsource]
      change (q₀+J x).1 ∈ D
      rw [hq]
      exact hQD hx.1
    have heq := harea (Z ⁻¹' T) hZT hZsource (fun _ => 1)
    simp only [mul_one,hq] at heq
    rw [Measure.restrict_prod_eq_prod_univ,← Measure.volume_eq_prod S F]
    rw [← (flatProductCoordinates_measurePreserving bS bF e).setLIntegral_comp_preimage_emb
      Z.toHomeomorph.measurableEmbedding]
    exact heq.symm

end ProductAreaChart

-- FiniteProjectiveCharts

end
end AffineBernstein
end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5} : type_of% @OAI.AffineBernstein.affineEpigraph_product_area_chart_oai.{u_1, u_2, u_3, u_4, u_5} := @OAI.AffineBernstein.affineEpigraph_product_area_chart_oai.{u_1, u_2, u_3, u_4, u_5}
