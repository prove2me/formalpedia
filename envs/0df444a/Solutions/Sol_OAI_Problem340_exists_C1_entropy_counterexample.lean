-- Prove2me | solution 1 for OAI.Problem340.exists_C1_entropy_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T23:13:29.260867+00:00
-- url     : https://prove2.me/submissions/e6bbcb18-40a9-44fc-9027-a4f005f435eb

import Mathlib
import Definitions.Def_C1EntropyCounterexample
import Definitions.Def_OAIQWEC000
import Theorems.Thm_OAI_Problem340_Construction_coverEntropy_realizedMap_eq_zero

instance p340Fact100 : Fact ((0 : ℝ) < 100) := ⟨by norm_num⟩

section
-- module Solutions.OAIQW_Problem340.StdSimplexShim
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
Port shim (not OpenAI's code). OpenAI's Mathlib takes the topological simplex of
`SimplexCategory.toTop` to be the structure `Convexity.StdSimplex ℝ (Fin (n+1))`; this Mathlib
takes it to be the subtype `stdSimplex ℝ (Fin (n+1))`. The port replaces OpenAI's
`Convexity.StdSimplex` by `OAI.SStd`, the subtype `stdSimplex R X` on a finite type, and this file
provides the part of the newer API that OpenAI's modules use, with `SStd.map` equal to
`stdSimplex.map`, so that `TopCat.toSSetObjEquiv` and its naturality apply unchanged.
-/

namespace OAI

namespace SStd

section Field

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {X : Type*} [Fintype X]

lemma weights_barycenter_apply [Nonempty X] (x : X) :
    (barycenter : SStd 𝕜 X).weights x = (Fintype.card X : 𝕜)⁻¹ := rfl

end Field

section Real

variable (M : Type*) [Fintype M]

lemma range_toFun_comp_weights_eq_stdSimplex :
    Set.range (fun t ↦ t.weights : SStd ℝ M → M → ℝ) = stdSimplex ℝ M := by
  ext f
  simp only [Set.mem_range, coe_weights]
  exact ⟨by rintro ⟨s, rfl⟩; exact s.2, fun hf => ⟨⟨f, hf⟩, rfl⟩⟩

lemma range_toFun_comp_weights_subset_closedBall :
    Set.range (fun t ↦ t.weights : SStd ℝ M → M → ℝ) ⊆ Metric.closedBall 0 1 := by
  rw [range_toFun_comp_weights_eq_stdSimplex]
  exact stdSimplex_subset_closedBall

lemma isBounded_range_toFun_comp_weights :
    Bornology.IsBounded (Set.range (fun t ↦ t.weights : SStd ℝ M → M → ℝ)) :=
  Metric.isBounded_closedBall.subset (range_toFun_comp_weights_subset_closedBall M)

lemma diam_range_toFun_comp_weights_subset_closedBall :
    Metric.diam (Set.range (fun t ↦ t.weights : SStd ℝ M → M → ℝ)) ≤ 1 := by
  rw [range_toFun_comp_weights_eq_stdSimplex]
  exact diam_stdSimplex_le

end Real

end SStd

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SimplexCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.RealSimplex

variable {Index : Type*} [Fintype Index]

@[simp] lemma barycenter_apply [Nonempty Index] (index : Index) :
    (SStd.barycenter : SStd ℝ Index) index = (Fintype.card Index : ℝ)⁻¹ :=
  SStd.weights_barycenter_apply index

end Problem340.RealSimplex

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.AffineSimplexGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.AffineSimplex

variable {E : Type*} {n : ℕ}

section Realization

variable [AddCommGroup E] [Module ℝ E]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma realize_mem_convexHull (v : ι → E) (p : SStd ℝ ι) :
    realize v p ∈ convexHull ℝ (Set.range v) :=
  realize_mem (convex_convexHull ℝ _) v
    (fun i => subset_convexHull ℝ _ (Set.mem_range_self i)) p

lemma barycenter_eq_sum [Nonempty ι] (v : ι → E) :
    barycenter v = (Fintype.card ι : ℝ)⁻¹ • ∑ i, v i := by
  simp [barycenter, realize, Finset.smul_sum]

end Realization

section SimplexTarget

variable {ι κ τ : Type*} [Fintype ι] [Fintype κ] [Fintype τ]

lemma realize_simplexRealizeMap {E : Type*} [AddCommGroup E] [Module ℝ E]
    (v : κ → E) (w : ι → SStd ℝ κ) (p : SStd ℝ ι) :
    realize v (simplexRealizeMap w p) = realize (fun i => realize v (w i)) p := by
  unfold realize
  simp_rw [simplexRealizeMap_apply, Finset.sum_smul, Finset.smul_sum, mul_smul]
  exact Finset.sum_comm

lemma simplexRealizeMap_assoc (v : κ → SStd ℝ τ)
    (w : ι → SStd ℝ κ) (p : SStd ℝ ι) :
    simplexRealizeMap v (simplexRealizeMap w p) =
      simplexRealizeMap (fun i => simplexRealizeMap v (w i)) p := by
  apply RealSimplex.coordinates_injective
  change (simplexRealizeMap v (simplexRealizeMap w p) : τ → ℝ) =
    (simplexRealizeMap (fun i => simplexRealizeMap v (w i)) p : τ → ℝ)
  simp only [simplexRealizeMap_coe]
  exact realize_simplexRealizeMap (fun j => (v j : τ → ℝ)) w p

lemma simplexRealizeMap_barycenter [Nonempty ι]
    (v : κ → SStd ℝ τ) (w : ι → SStd ℝ κ) :
    simplexRealizeMap v (simplexBarycenter w) =
      simplexBarycenter (fun i => simplexRealizeMap v (w i)) :=
  simplexRealizeMap_assoc v w SStd.barycenter

end SimplexTarget

end Problem340.AffineSimplex

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.HomologyCycle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory

namespace Problem340

section ModuleCycles

variable {R : Type*} [Ring R]

theorem moduleHomologyClass_eq_zero_iff (S : ShortComplex (ModuleCat R))
    (z : S.X₂) (hz : S.g.hom z = 0) :
    moduleHomologyClass S z hz = 0 ↔ ∃ w : S.X₁, S.f.hom w = z := by
  unfold moduleHomologyClass
  conv_lhs =>
    exact propext S.moduleCatHomologyIso.toLinearEquiv.symm.map_eq_zero_iff
  change (Submodule.Quotient.mk (⟨z, LinearMap.mem_ker.mpr hz⟩ : LinearMap.ker S.g.hom) :
    LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w, congrArg Subtype.val hw⟩
  · rintro ⟨w, hw⟩
    refine ⟨w, ?_⟩
    exact Subtype.ext hw

theorem moduleHomologyClass_eq_pi (S : ShortComplex (ModuleCat R))
    (z : S.X₂) (hz : S.g.hom z = 0) :
    moduleHomologyClass S z hz = S.homologyπ.hom
      (S.moduleCatCyclesIso.inv.hom ⟨z, LinearMap.mem_ker.mpr hz⟩) := by
  exact (S.moduleCatCyclesIso_inv_π_apply ⟨z, LinearMap.mem_ker.mpr hz⟩).symm

theorem moduleHomologyClass_map {S T : ShortComplex (ModuleCat R)}
    (φ : S ⟶ T) (z : S.X₂) (hz : S.g.hom z = 0)
    (hz' : T.g.hom (φ.τ₂.hom z) = 0) :
    (ShortComplex.homologyMap φ).hom (moduleHomologyClass S z hz) =
      moduleHomologyClass T (φ.τ₂.hom z) hz' := by
  rw [moduleHomologyClass_eq_pi, moduleHomologyClass_eq_pi]
  let zs := S.moduleCatCyclesIso.inv.hom ⟨z, LinearMap.mem_ker.mpr hz⟩
  let zt := T.moduleCatCyclesIso.inv.hom ⟨φ.τ₂.hom z, LinearMap.mem_ker.mpr hz'⟩
  have hs : S.iCycles.hom zs = z :=
    S.moduleCatCyclesIso_inv_iCycles_apply ⟨z, LinearMap.mem_ker.mpr hz⟩
  have ht : T.iCycles.hom zt = φ.τ₂.hom z :=
    T.moduleCatCyclesIso_inv_iCycles_apply ⟨φ.τ₂.hom z, LinearMap.mem_ker.mpr hz'⟩
  have hc : (ShortComplex.cyclesMap φ).hom zs = zt := by
    apply (ModuleCat.mono_iff_injective T.iCycles).mp inferInstance
    have h := congrArg (fun k : S.cycles ⟶ T.X₂ => k.hom zs)
      (ShortComplex.cyclesMap_i φ)
    change T.iCycles.hom ((ShortComplex.cyclesMap φ).hom zs) =
      φ.τ₂.hom (S.iCycles.hom zs) at h
    simpa only [hs, ht] using h
  have h := congrArg (fun k : S.cycles ⟶ T.homology => k.hom zs)
    (ShortComplex.homologyπ_naturality φ)
  change (ShortComplex.homologyMap φ).hom (S.homologyπ.hom zs) =
    T.homologyπ.hom ((ShortComplex.cyclesMap φ).hom zs) at h
  rw [hc] at h
  exact h

end ModuleCycles

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.BarycentricSubdivision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.SingularSubdivision

lemma affine_centers {k l : ℕ} (v : Fin (k + 1) → StandardSimplex l)
    (n : ℕ) (p : Fin (n + 1) → StandardSimplex k) :
    AffineSimplex.simplexRealizeMap v (simplexCenters k n p) =
      simplexCenters l n (AffineSimplex.simplexRealizeMap v ∘ p) :=
  AffineSimplex.simplexRealizeMap_barycenter v p

end Problem340.SingularSubdivision

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SimplexSingularRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.SimplexSingularRealization

open SingularSubdivision

theorem affineMap_realize (k l n : ℕ) (w : Fin (k + 1) → Simplex l)
    (c : Chains (Simplex k) (n + 1)) :
    ((realSingularChainMap (AffineSimplex.simplexRealizeMap w)
      (AffineSimplex.simplexRealizeMap w).continuous).f n).hom (realize k n c) =
      realize l n (mapVertices (AffineSimplex.simplexRealizeMap w) (n + 1) c) := by
  have h : ((realSingularChainMap (AffineSimplex.simplexRealizeMap w)
      (AffineSimplex.simplexRealizeMap w).continuous).f n).hom.comp (realize k n) =
      (realize l n).comp (mapVertices (AffineSimplex.simplexRealizeMap w) (n + 1)) := by
    apply linearMap_ext
    intro v
    change ((realSingularChainMap (AffineSimplex.simplexRealizeMap w)
      (AffineSimplex.simplexRealizeMap w).continuous).f n).hom
      (realize k n (generator v)) = _
    rw [realize_generator, SingularChainFormulas.simplexChain_map]
    have he : (AffineSimplex.simplexRealizeMap w).comp
        (AffineSimplex.simplexRealizeMap v) =
        AffineSimplex.simplexRealizeMap (AffineSimplex.simplexRealizeMap w ∘ v) := by
      ext p : 1
      exact AffineSimplex.simplexRealizeMap_assoc w v p
    simp only [LinearMap.comp_apply, mapVertices_generator, realize_generator]
    rw [he]
  exact LinearMap.congr_fun h c

end Problem340.SimplexSingularRealization

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.HomologyConstant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory

namespace Problem340

theorem realSingularHomology_subsingleton_of_totallyDisconnected
    (n : ℕ) (hn : n ≠ 0) (X : Type) [TopologicalSpace X]
    [TotallyDisconnectedSpace X] : Subsingleton (RealSingularHomology n X) := by
  exact ModuleCat.subsingleton_of_isZero
    (AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      (ModuleCat ℝ) n (ModuleCat.of ℝ ℝ) (TopCat.of X) hn)

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SingularAcyclicModels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Simplicial

namespace Problem340.SingularAcyclicModels

lemma homotopyApp_naturality (f g : singularFunctor ⟶ singularFunctor)
    (h : ∀ X, (f.app X).f 0 = (g.app X).f 0)
    {X Y : TopCat.{0}} (u : X ⟶ Y) (i j : ℕ) :
    (singularFunctor.map u).f i ≫ (homotopyApp f g h Y).hom i j =
      (homotopyApp f g h X).hom i j ≫ (singularFunctor.map u).f j :=
  ((naturalHomotopy f g h).hom i j).naturality u

end Problem340.SingularAcyclicModels

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.ActualSingularSubdivisionMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory

namespace Problem340.ActualSingularSubdivision

alias chainMap_app_f := subdivisionChainMap_f

alias chainMap_app_zero := subdivisionChainMap_zero

end Problem340.ActualSingularSubdivision

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.Clock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.Clock

lemma contDiff_profile {n : ℕ∞} : ContDiff ℝ n profile := by
  unfold profile
  exact (((profileCutoff.contDiff.mul contDiff_id).div_const 4).add contDiff_const).sub
    profileCutoff.contDiff

lemma localBarrier_eq_profile (x : ℝ) : localBarrier x = profile (x ^ 2) := rfl

lemma coordinate_sq (t : ℝ) :
    coordinate t ^ 2 = 450 * (1 + Real.cos (2 * Real.pi * t / 100)) := by
  have hangle : Real.pi * (t - 50) / 100 = Real.pi * t / 100 - Real.pi / 2 := by ring
  have hcos := Real.cos_two_mul (Real.pi * t / 100)
  have hdouble : 2 * (Real.pi * t / 100) = 2 * Real.pi * t / 100 := by ring
  rw [hdouble] at hcos
  unfold coordinate
  rw [hangle, Real.sin_sub_pi_div_two]
  nlinarith

lemma contDiff_ambientBarrier {n : ℕ∞} : ContDiff ℝ n ambientBarrier := by
  apply contDiff_profile.comp
  exact contDiff_const.mul (contDiff_const.add (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contDiff)

lemma ambientBarrier_on_circle (t : ℝ) (x : EuclideanSpace ℝ (Fin 2))
    (hx : x 0 = Real.cos (2 * Real.pi * t / 100)) :
    ambientBarrier x = barrier t := by
  rw [ambientBarrier, hx, barrier, localBarrier_eq_profile, coordinate_sq]

lemma contDiff_increment {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ∞} {t e : E → ℝ} (ht : ContDiff ℝ n t) (he : ContDiff ℝ n e) :
    ContDiff ℝ n (fun x => increment (t x) (e x)) := by
  exact (contDiff_barrier.comp ht).add
    ((contDiff_const.sub (contDiff_barrier.comp ht)).mul he)

end Problem340.Clock

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.PredictionDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Problem340.Prediction

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem differentiableAt_iterate_and_norm_le_on {G : E → E} {B : ℝ} {s : Set E}
    (hG : ∀ x ∈ s, DifferentiableAt 𝕜 G x) (hmap : Set.MapsTo G s s)
    (hB : 0 ≤ B) (hbound : ∀ x ∈ s, ‖fderiv 𝕜 G x‖ ≤ B)
    (m : ℕ) (x : E) (hx : x ∈ s) :
    DifferentiableAt 𝕜 (G^[m]) x ∧ ‖fderiv 𝕜 (G^[m]) x‖ ≤ B ^ m := by
  induction m generalizing x with
  | zero =>
      constructor
      · exact differentiableAt_id
      · simpa using ContinuousLinearMap.norm_id_le (𝕜 := 𝕜) (E := E)
  | succ m hm =>
      obtain ⟨hd, hn⟩ := hm (G x) (hmap hx)
      rw [Function.iterate_succ]
      refine ⟨hd.comp x (hG x hx), ?_⟩
      rw [fderiv_comp x hd (hG x hx)]
      calc
        ‖(fderiv 𝕜 (G^[m]) (G x)).comp (fderiv 𝕜 G x)‖
            ≤ ‖fderiv 𝕜 (G^[m]) (G x)‖ * ‖fderiv 𝕜 G x‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ B ^ m * B := mul_le_mul hn (hbound x hx)
          (norm_nonneg _) (pow_nonneg hB _)
        _ = B ^ (m + 1) := (pow_succ B m).symm

end Problem340.Prediction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SphereCutoffs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.SphereCutoffs

theorem preparationCutoffAmbient_nonneg (x : SphereAmbient) :
    0 ≤ preparationCutoffAmbient x :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem preparationCutoffAmbient_le_one (x : SphereAmbient) :
    preparationCutoffAmbient x ≤ 1 := by
  exact (mul_le_of_le_one_left (Real.smoothTransition.nonneg _)
    (Real.smoothTransition.le_one _)).trans (Real.smoothTransition.le_one _)

theorem clockGateAmbient_eq_one {x : SphereAmbient} (h : -7 / 25 ≤ x 2) :
    clockGateAmbient x = 1 := by
  apply Real.smoothTransition.one_of_one_le
  linarith

theorem preparationCutoffAmbient_eq_zero_of_low {x : SphereAmbient}
    (h : x 2 ≤ -4 / 5) : preparationCutoffAmbient x = 0 := by
  unfold preparationCutoffAmbient
  rw [Real.smoothTransition.zero_of_nonpos (by linarith : 5 * x 2 + 4 ≤ 0), zero_mul]

theorem preparationCutoffAmbient_eq_zero_of_high {x : SphereAmbient}
    (h : 1 / 2 ≤ x 2) : preparationCutoffAmbient x = 0 := by
  unfold preparationCutoffAmbient
  rw [Real.smoothTransition.zero_of_nonpos (by linarith : 1 - 2 * x 2 ≤ 0), mul_zero]

end Problem340.SphereCutoffs

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SphereDoubling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.SphereDoubling

lemma stereoCoordinate_ambientMap {x : Ambient} (hx : x 2 ≠ 1) :
    stereoCoordinate (ambientMap x) = stereoCoordinate x ^ 2 := by
  have hd : (1 : ℂ) + (x 2 : ℂ) ^ 2 ≠ 0 := by
    simpa using (Complex.ofReal_ne_zero.mpr (ne_of_gt (denominator_pos x)))
  have hz : (1 : ℂ) - (x 2 : ℂ) ≠ 0 := by
    simpa using (Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm hx)))
  change (((((x 0 ^ 2 - x 1 ^ 2) / (1 + x 2 ^ 2) : ℝ) : ℂ) +
    Complex.I * (((2 * x 0 * x 1) / (1 + x 2 ^ 2) : ℝ) : ℂ)) /
    (1 - (((2 * x 2) / (1 + x 2 ^ 2) : ℝ) : ℂ))) = _
  unfold stereoCoordinate
  push_cast
  have hden : (1 : ℂ) - 2 * (x 2 : ℂ) / (1 + (x 2 : ℂ) ^ 2) =
      (1 - (x 2 : ℂ)) ^ 2 / (1 + (x 2 : ℂ) ^ 2) := by
    field_simp
    ring
  rw [hden]
  field_simp [hd, hz]
  ring_nf
  simp [Complex.I_sq, sub_eq_add_neg]

lemma stereoCoordinate_sphereMap {x : Sphere} (hx : x ≠ north) :
    stereoCoordinate (sphereMap x).val = stereoCoordinate x.val ^ 2 := by
  exact stereoCoordinate_ambientMap (mt (eq_north_iff x).mpr hx)

end Problem340.SphereDoubling

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.AmbientPrediction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.AmbientPrediction

@[fun_prop]
theorem contDiff_predictor {n : ℕ∞} : ContDiff ℝ n predictor := by
  exact (contDiff_fst.add (Clock.contDiff_increment contDiff_fst
    (SphereCutoffs.contDiff_clockGateAmbient.comp contDiff_snd))).prodMk
      ((SphereDoubling.contDiff_ambientMap n).comp contDiff_snd)

theorem predictor_equivariant (x : Ambient) :
    predictor (x + (100, 0)) = predictor x + (100, 0) := by
  apply Prod.ext
  · change x.1 + 100 + Clock.increment (x.1 + 100)
      (SphereCutoffs.clockGateAmbient (x.2 + 0)) =
        (x.1 + Clock.increment x.1 (SphereCutoffs.clockGateAmbient x.2)) + 100
    rw [add_zero]
    have hi := Clock.increment_periodic (SphereCutoffs.clockGateAmbient x.2) x.1
    dsimp at hi
    rw [hi]
    ring
  · simp [predictor]

@[fun_prop]
theorem contDiff_clockPrediction (m : ℕ) {n : ℕ∞} :
    ContDiff ℝ n (clockPrediction m) :=
by
  have hi : ContDiff ℝ n (predictor^[m]) := by
    induction m with
    | zero => simpa using (contDiff_id : ContDiff ℝ n (id : Ambient → Ambient))
    | succ m ih =>
      rw [Function.iterate_succ]
      exact ih.comp contDiff_predictor
  exact hi.fst

theorem exists_derivative_bound :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ x ∈ cylinder, ‖fderiv ℝ predictor x‖ ≤ B := by
  have hperiod (z : SphereAmbient) :
      Function.Periodic (fun t => fderiv ℝ predictor (t, z)) 100 := by
    intro t
    have heq : fderiv ℝ predictor ((t, z) + (100, 0)) =
        fderiv ℝ predictor (t, z) := by
      calc
        _ = fderiv ℝ (fun y => predictor (y + (100, 0))) (t, z) :=
          (fderiv_comp_add_right (100, 0)).symm
        _ = fderiv ℝ (fun y => predictor y + (100, 0)) (t, z) :=
          congrArg (fun f => fderiv ℝ f (t, z)) (funext predictor_equivariant)
        _ = fderiv ℝ predictor (t, z) := fderiv_add_const (100, 0)
    simpa using heq
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc.prod (isCompact_sphere (0 : SphereAmbient) 1)).exists_bound_of_continuousOn
      ((contDiff_predictor (n := 1)).continuous_fderiv one_ne_zero).continuousOn
  refine ⟨max 1 C, le_max_left _ _, ?_⟩
  intro x hx
  obtain ⟨r, hr, heq⟩ := (hperiod x.2).exists_mem_Ico₀
    (by norm_num : (0 : ℝ) < 100) x.1
  rw [show fderiv ℝ predictor x = fderiv ℝ predictor (r, x.2) from heq]
  exact (hC (r, x.2) ⟨⟨hr.1, hr.2.le⟩, hx.2⟩).trans (le_max_right _ _)

end Problem340.AmbientPrediction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.Embedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Topology

namespace Problem340

theorem isEmbedding_standardEmbedding (q : ℕ) :
    IsEmbedding (standardEmbedding q) := by
  exact IsEmbedding.subtypeVal.prodMap
    (IsEmbedding.piMap fun _ => IsEmbedding.subtypeVal)

@[continuity, fun_prop]
theorem continuous_standardEmbedding (q : ℕ) : Continuous (standardEmbedding q) :=
  (isEmbedding_standardEmbedding q).continuous

theorem continuous_iff_standardEmbedding {X : Type*} [TopologicalSpace X]
    (q : ℕ) (f : X → CounterexampleManifold q) :
    Continuous f ↔ Continuous (standardEmbedding q ∘ f) :=
  (isEmbedding_standardEmbedding q).continuous_iff

theorem continuous_of_local_contDiff_extension {q : ℕ}
    (f : CounterexampleManifold q → CounterexampleManifold q)
    (hlocal : ∀ x : CounterexampleManifold q,
      ∃ U : Set (CounterexampleAmbient q),
        IsOpen U ∧ standardEmbedding q x ∈ U ∧
          ∃ F : CounterexampleAmbient q → CounterexampleAmbient q,
            ContDiffOn ℝ 1 F U ∧
              ∀ y : CounterexampleManifold q,
                standardEmbedding q y ∈ U →
                  standardEmbedding q (f y) = F (standardEmbedding q y)) :
    Continuous f := by
  apply (continuous_iff_standardEmbedding q f).2
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨U, hU, hxU, F, hF, hcomm⟩ := hlocal x
  have hcont : ContinuousAt (F ∘ standardEmbedding q) x :=
    (hF.contDiffAt (hU.mem_nhds hxU)).continuousAt.comp
      (continuous_standardEmbedding q).continuousAt
  apply hcont.congr_of_eventuallyEq
  filter_upwards [(continuous_standardEmbedding q).continuousAt.preimage_mem_nhds
    (hU.mem_nhds hxU)] with y hy
  exact hcomm y hy

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.AmbientRetraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ContDiff

namespace Problem340.AmbientRetraction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem contDiffAt_normalize {n : ℕ∞ω} {x : E} (hx : x ≠ 0) :
    ContDiffAt ℝ n normalize x := by
  exact ((contDiffAt_id.norm ℝ hx).inv (norm_ne_zero_iff.mpr hx)).smul contDiffAt_id

theorem normalize_mem_sphere {x : E} (hx : x ≠ 0) :
    normalize x ∈ Metric.sphere (0 : E) 1 := by
  rw [mem_sphere_zero_iff_norm, normalize, norm_smul, norm_inv, norm_norm]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)

theorem normalize_eq_self {x : E} (hx : x ∈ Metric.sphere (0 : E) 1) :
    normalize x = x := by
  rw [normalize, mem_sphere_zero_iff_norm.mp hx, inv_one, one_smul]

theorem norm_normalize_le_one (x : E) : ‖normalize x‖ ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx, normalize]
  · exact le_of_eq (mem_sphere_zero_iff_norm.mp (normalize_mem_sphere hx))

theorem norm_normalize_sub_le {x : E} (hx : x ≠ 0) (y : E) :
    ‖normalize y - normalize x‖ ≤ (2 / ‖x‖) * ‖y - x‖ := by
  have hid : ‖x‖ • (normalize y - normalize x) =
      (‖x‖ - ‖y‖) • normalize y + (y - x) := by
    rw [smul_sub, sub_smul, norm_smul_normalize, norm_smul_normalize]
    abel
  have hscale : ‖x‖ * ‖normalize y - normalize x‖ ≤ 2 * ‖y - x‖ := by
    calc
      ‖x‖ * ‖normalize y - normalize x‖ =
          ‖‖x‖ • (normalize y - normalize x)‖ := by rw [norm_smul, norm_norm]
      _ = ‖(‖x‖ - ‖y‖) • normalize y + (y - x)‖ := congrArg norm hid
      _ ≤ ‖(‖x‖ - ‖y‖) • normalize y‖ + ‖y - x‖ := norm_add_le _ _
      _ = |‖x‖ - ‖y‖| * ‖normalize y‖ + ‖y - x‖ := by
        rw [norm_smul, Real.norm_eq_abs]
      _ ≤ |‖x‖ - ‖y‖| + ‖y - x‖ := by
        nlinarith [norm_normalize_le_one y, abs_nonneg (‖x‖ - ‖y‖)]
      _ ≤ 2 * ‖y - x‖ := by
        have hnorm := abs_norm_sub_norm_le x y
        rw [norm_sub_rev x y] at hnorm
        linarith
  calc
    ‖normalize y - normalize x‖ ≤ (2 * ‖y - x‖) / ‖x‖ :=
      (le_div_iff₀ (norm_pos_iff.mpr hx)).mpr (by nlinarith [hscale])
    _ = (2 / ‖x‖) * ‖y - x‖ := by ring

theorem contDiffAt_cylinder {n : ℕ∞ω} {x : ℝ × E} (hx : x.2 ≠ 0) :
    ContDiffAt ℝ n cylinder x := by
  exact contDiffAt_fst.prodMk ((contDiffAt_normalize hx).comp x contDiffAt_snd)

theorem norm_cylinder_sub_le_four {x : ℝ × E} (hx : (1 / 2 : ℝ) ≤ ‖x.2‖)
    (y : ℝ × E) : ‖cylinder y - cylinder x‖ ≤ 4 * ‖y - x‖ := by
  have hxpos : 0 < ‖x.2‖ := by linarith
  have hratio : 2 / ‖x.2‖ ≤ 4 := (div_le_iff₀ hxpos).mpr (by linarith)
  change max ‖y.1 - x.1‖ ‖normalize y.2 - normalize x.2‖ ≤ 4 * ‖y - x‖
  apply max_le
  · have hfst := norm_fst_le (y - x)
    change ‖y.1 - x.1‖ ≤ ‖y - x‖ at hfst
    nlinarith [norm_nonneg (y - x)]
  · calc
      ‖normalize y.2 - normalize x.2‖ ≤ (2 / ‖x.2‖) * ‖y.2 - x.2‖ :=
        norm_normalize_sub_le (norm_pos_iff.mp hxpos) _
      _ ≤ 4 * ‖y.2 - x.2‖ := mul_le_mul_of_nonneg_right hratio (norm_nonneg _)
      _ ≤ 4 * ‖y - x‖ := mul_le_mul_of_nonneg_left (norm_snd_le (y - x)) (by norm_num)

theorem norm_fderiv_cylinder_le_four {x : ℝ × E} (hx : (1 / 2 : ℝ) ≤ ‖x.2‖) :
    ‖fderiv ℝ cylinder x‖ ≤ 4 := by
  apply norm_fderiv_le_of_lip' ℝ (by norm_num)
  exact Filter.Eventually.of_forall (norm_cylinder_sub_le_four hx)

@[simp]
theorem cylinder_eq_self {x : ℝ × E} (hx : ‖x.2‖ = 1) : cylinder x = x := by
  apply Prod.ext
  · rfl
  · exact normalize_eq_self (mem_sphere_zero_iff_norm.mpr hx)

omit [InnerProductSpace ℝ E] in
theorem isOpen_cylinderDomain : IsOpen (cylinderDomain (E := E)) :=
  isOpen_lt continuous_const (continuous_norm.comp continuous_snd)

theorem mapsTo_normalizedPredictor
    (G : ℝ × E → ℝ × E)
    (hG : ∀ x : ℝ × E, ‖x.2‖ = 1 → ‖(G x).2‖ = 1) :
    Set.MapsTo (G ∘ cylinder) cylinderDomain cylinderDomain := by
  intro x hx
  change (1 / 2 : ℝ) < ‖x.2‖ at hx
  have hxne : x.2 ≠ 0 := norm_pos_iff.mp (by linarith [hx])
  have hn : ‖(cylinder x).2‖ = 1 :=
    mem_sphere_zero_iff_norm.mp (normalize_mem_sphere hxne)
  change (1 / 2 : ℝ) < ‖(G (cylinder x)).2‖
  rw [hG _ hn]
  norm_num

theorem contDiffOn_normalizedPredictor {n : ℕ∞ω}
    (G : ℝ × E → ℝ × E) (hG : ContDiff ℝ n G) :
    ContDiffOn ℝ n (G ∘ cylinder) cylinderDomain := by
  intro x hx
  change (1 / 2 : ℝ) < ‖x.2‖ at hx
  apply ContDiffAt.contDiffWithinAt
  exact hG.contDiffAt.comp x (contDiffAt_cylinder
    (norm_pos_iff.mp (by linarith [hx])))

theorem normalizedPredictor_iterate_eq
    (G : ℝ × E → ℝ × E)
    (hG : ∀ x : ℝ × E, ‖x.2‖ = 1 → ‖(G x).2‖ = 1)
    {x : ℝ × E} (hx : ‖x.2‖ = 1) (n : ℕ) :
    (G ∘ cylinder)^[n] x = G^[n] x := by
  have hinv : Set.MapsTo G {x : ℝ × E | ‖x.2‖ = 1} {x : ℝ × E | ‖x.2‖ = 1} := hG
  induction n with
  | zero => rfl
  | succ n hn =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hn]
      change G (cylinder (G^[n] x)) = G (G^[n] x)
      rw [cylinder_eq_self (hinv.iterate n hx)]

theorem normalizedPredictor_iterate_succ_eq
    (G : ℝ × E → ℝ × E)
    (hG : ∀ x : ℝ × E, ‖x.2‖ = 1 → ‖(G x).2‖ = 1)
    {x : ℝ × E} (hx : x.2 ≠ 0) (n : ℕ) :
    (G ∘ cylinder)^[n + 1] x = G^[n + 1] (cylinder x) := by
  rw [Function.iterate_succ_apply, Function.comp_apply]
  have hn : ‖(G (cylinder x)).2‖ = 1 :=
    hG _ (mem_sphere_zero_iff_norm.mp (normalize_mem_sphere hx))
  rw [normalizedPredictor_iterate_eq G hG hn n, Function.iterate_succ_apply]

end Problem340.AmbientRetraction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.CoordinateGoodCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric
open scoped unitInterval

namespace Problem340
namespace CoordinateGoodCover

theorem GoodCover.iUnion_eq_univ {ι X : Type*} [TopologicalSpace X]
    (U : GoodCover ι X) : (⋃ i, U.carrier i) = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact U.covers x

end CoordinateGoodCover
end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.FiniteSpectrumBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340

theorem pairedEigenvalue_modulus_le_opNorm
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (A : V →L[ℝ] V) {a b : ℝ} {u v : V}
    (huv : u ≠ 0 ∨ v ≠ 0)
    (hu : A u = a • u - b • v)
    (hv : A v = b • u + a • v) :
    Real.sqrt (a ^ 2 + b ^ 2) ≤ ‖A‖ := by
  have hid : ‖A u‖ ^ 2 + ‖A v‖ ^ 2 =
      (a ^ 2 + b ^ 2) * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
    rw [hu, hv, norm_sub_sq_real, norm_add_sq_real]
    simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      real_inner_smul_left, real_inner_smul_right]
    ring
  have hp : 0 < ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
    rcases huv with h | h
    · have := norm_pos_iff.mpr h
      positivity
    · have := norm_pos_iff.mpr h
      positivity
  have hAu : ‖A u‖ ^ 2 ≤ ‖A‖ ^ 2 * ‖u‖ ^ 2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg (A u)) (A.le_opNorm u) 2
  have hAv : ‖A v‖ ^ 2 ≤ ‖A‖ ^ 2 * ‖v‖ ^ 2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg (A v)) (A.le_opNorm v) 2
  have hs : a ^ 2 + b ^ 2 ≤ ‖A‖ ^ 2 := by
    apply (mul_le_mul_iff_left₀ hp).mp
    nlinarith [hid]
  exact (Real.sqrt_le_iff).2 ⟨norm_nonneg A, hs⟩

theorem exists_bound_pairedEigenvalue_modulus
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (A : V →ₗ[ℝ] V) :
    ∃ C : ℝ, ∀ (a b : ℝ) (u v : V),
      (u ≠ 0 ∨ v ≠ 0) →
      A u = a • u - b • v →
      A v = b • u + a • v →
      Real.sqrt (a ^ 2 + b ^ 2) ≤ C := by
  let E := EuclideanSpace ℝ (Fin (Module.finrank ℝ V))
  let e : V ≃ₗ[ℝ] E := LinearEquiv.ofFinrankEq V E finrank_euclideanSpace_fin.symm
  let B : E →L[ℝ] E := LinearMap.toContinuousLinearMap (e.conj A)
  refine ⟨‖B‖, ?_⟩
  intro a b u v huv hu hv
  apply pairedEigenvalue_modulus_le_opNorm B (u := e u) (v := e v)
  · simpa only [ne_eq, e.map_eq_zero_iff] using huv
  · change e (A (e.symm (e u))) = a • e u - b • e v
    simpa only [e.symm_apply_apply, map_sub, map_smul] using congrArg e hu
  · change e (A (e.symm (e v))) = b • e u + a • e v
    simpa only [e.symm_apply_apply, map_add, map_smul] using congrArg e hv

theorem bddAbove_total_pairedEigenvalue_moduli
    {V : ℕ → Type*} [∀ n, AddCommGroup (V n)] [∀ n, Module ℝ (V n)]
    [∀ n, FiniteDimensional ℝ (V n)]
    (A : ∀ n, V n →ₗ[ℝ] V n) (N : ℕ)
    (hvanish : ∀ n, N < n → Subsingleton (V n)) :
    BddAbove {r : ℝ | ∃ n : ℕ, ∃ a b : ℝ, ∃ u v : V n,
      (u ≠ 0 ∨ v ≠ 0) ∧
      A n u = a • u - b • v ∧
      A n v = b • u + a • v ∧
      r = Real.sqrt (a ^ 2 + b ^ 2)} := by
  classical
  choose C hC using fun n => exists_bound_pairedEigenvalue_modulus (A n)
  obtain ⟨M, hM⟩ := (Set.finite_range (fun n : Fin (N + 1) => C n)).bddAbove
  refine ⟨M, ?_⟩
  rintro r ⟨n, a, b, u, v, huv, hu, hv, rfl⟩
  have hn : n < N + 1 := by
    by_contra h
    have hi : N < n := by omega
    let := hvanish n hi
    rcases huv with h | h
    · exact h (Subsingleton.elim _ _)
    · exact h (Subsingleton.elim _ _)
  exact (hC n a b u v huv hu hv).trans (hM ⟨⟨n, hn⟩, rfl⟩)

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.FiniteSimplicialHomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Problem340

theorem finiteDimensional_shortComplex_homology
    (S : ShortComplex (ModuleCat ℝ)) [FiniteDimensional ℝ S.X₂] :
    FiniteDimensional ℝ S.homology := by
  have : FiniteDimensional ℝ S.moduleCatLeftHomologyData.H := by
    change FiniteDimensional ℝ (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles)
    infer_instance
  exact Module.Finite.equiv S.moduleCatHomologyIso.toLinearEquiv.symm

theorem finiteDimensional_normalized_real_chains
    (X : SSet) [X.Finite] (n : ℕ) :
    FiniteDimensional ℝ ((X.normalizedChainComplex (ModuleCat.of ℝ ℝ)).X n) := by
  let R : ModuleCat ℝ := ModuleCat.of ℝ ℝ
  let e : (X.normalizedChainComplex R).X n ≅ (∐ fun _ : X.nonDegenerate n => R) :=
    (X.isColimitCofanNormalizedChainComplex R n).coconePointUniqueUpToIso
      (coproductIsCoproduct _)
  have : FiniteDimensional ℝ (∐ fun _ : X.nonDegenerate n => R : ModuleCat ℝ) := by
    infer_instance
  exact Module.Finite.equiv e.toLinearEquiv.symm

theorem finiteDimensional_real_simplicial_homology
    (X : SSet) [X.Finite] (n : ℕ) :
    FiniteDimensional ℝ (X.homology (ModuleCat.of ℝ ℝ) n : ModuleCat ℝ) := by
  let R : ModuleCat ℝ := ModuleCat.of ℝ ℝ
  have : FiniteDimensional ℝ ((X.normalizedChainComplex R).sc n).X₂ :=
    finiteDimensional_normalized_real_chains X n
  have : FiniteDimensional ℝ ((X.normalizedChainComplex R).homology n) :=
    finiteDimensional_shortComplex_homology ((X.normalizedChainComplex R).sc n)
  let e := asIso (HomologicalComplex.homologyMap (X.toNormalizedChainComplex R) n)
  exact Module.Finite.equiv e.toLinearEquiv.symm

theorem real_simplicial_homology_finite_support (X : SSet) [X.Finite] :
    ∃ N : ℕ, ∀ n, N ≤ n → Subsingleton (X.homology (ModuleCat.of ℝ ℝ) n : ModuleCat ℝ) := by
  obtain ⟨N, hN⟩ := X.hasDimensionLT_of_finite
  let := hN
  refine ⟨N, fun n hn => ?_⟩
  exact ModuleCat.isZero_iff_subsingleton.mp
    (X.isZero_homology_of_hasDimensionLT (ModuleCat.of ℝ ℝ) n N hn)

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.FiniteGoodCoverHomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Problem340.FiniteGoodCover

attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryProducts

lemma finiteDimensional_of_exact (S : ShortComplex (ModuleCat ℝ))
    (hS : S.Exact) [FiniteDimensional ℝ S.X₁] [FiniteDimensional ℝ S.X₃] :
    FiniteDimensional ℝ S.X₂ := by
  have : FiniteDimensional ℝ (LinearMap.ker S.g.hom) := by
    rw [← hS.moduleCat_range_eq_ker]
    infer_instance
  have : FiniteDimensional ℝ (S.X₂ ⧸ LinearMap.ker S.g.hom) :=
    Module.Finite.equiv S.g.hom.quotKerEquivRange.symm
  exact Module.Finite.of_submodule_quotient (LinearMap.ker S.g.hom)

lemma isZero_of_exact (S : ShortComplex (ModuleCat ℝ)) (hS : S.Exact)
    (h₁ : IsZero S.X₁) (h₃ : IsZero S.X₃) : IsZero S.X₂ := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  have := ModuleCat.isZero_iff_subsingleton.mp h₁
  have := ModuleCat.isZero_iff_subsingleton.mp h₃
  have hz : ∀ x : S.X₂, x = 0 := by
    intro x
    obtain ⟨y, hy⟩ := S.moduleCat_exact_iff.mp hS x (Subsingleton.elim _ _)
    rw [Subsingleton.elim y 0, map_zero] at hy
    exact hy.symm
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

lemma finiteHomology_biprod {C D : ChainComplex (ModuleCat ℝ) ℕ}
    (hC : FiniteHomology C) (hD : FiniteHomology D) : FiniteHomology (C ⊞ D) := by
  have e (n : ℕ) : (C ⊞ D).homology n ≅
      ModuleCat.of ℝ (C.homology n × D.homology n) :=
    (HomologicalComplex.homologyFunctor (ModuleCat ℝ) (ComplexShape.down ℕ) n).mapBiprod C D ≪≫
      ModuleCat.biprodIsoProd _ _
  constructor
  · intro n
    have := hC.1 n
    have := hD.1 n
    exact Module.Finite.equiv (e n).toLinearEquiv.symm
  · obtain ⟨NC, hNC⟩ := hC.2
    obtain ⟨ND, hND⟩ := hD.2
    refine ⟨max NC ND, fun n hn => ?_⟩
    have := ModuleCat.isZero_iff_subsingleton.mp (hNC n ((le_max_left _ _).trans hn))
    have := ModuleCat.isZero_iff_subsingleton.mp (hND n ((le_max_right _ _).trans hn))
    exact IsZero.of_iso (ModuleCat.isZero_iff_subsingleton.mpr inferInstance) (e n)

lemma finiteHomology_of_shortExact
    (S : ShortComplex (ChainComplex (ModuleCat ℝ) ℕ)) (hS : S.ShortExact)
    (h₁ : FiniteHomology S.X₁) (h₂ : FiniteHomology S.X₂) : FiniteHomology S.X₃ := by
  constructor
  · intro n
    cases n with
    | zero =>
      have := h₂.1 0
      have := hS.epi_g
      have : Epi (HomologicalComplex.homologyMap S.g 0) :=
        HomologicalComplex.epi_homologyMap_of_epi_of_not_rel S.g 0 (by simp)
      exact Module.Finite.of_surjective (HomologicalComplex.homologyMap S.g 0).hom
        ((ModuleCat.epi_iff_surjective _).mp inferInstance)
    | succ n =>
      have := h₂.1 (n + 1)
      have := h₁.1 n
      exact finiteDimensional_of_exact _ (hS.homology_exact₃ (n + 1) n (by simp))
  · obtain ⟨N₁, hN₁⟩ := h₁.2
    obtain ⟨N₂, hN₂⟩ := h₂.2
    refine ⟨max (N₁ + 1) N₂, fun n hn => ?_⟩
    have hn₁ : N₁ + 1 ≤ n := (le_max_left _ _).trans hn
    have hn₂ : N₂ ≤ n := (le_max_right _ _).trans hn
    cases n with
    | zero => omega
    | succ n =>
      exact isZero_of_exact _ (hS.homology_exact₃ (n + 1) n (by simp))
        (hN₂ (n + 1) hn₂) (hN₁ n (by omega))

lemma finiteHomology_of_quasiIso {C D : ChainComplex (ModuleCat ℝ) ℕ}
    (f : C ⟶ D) [QuasiIso f] (hC : FiniteHomology C) : FiniteHomology D := by
  have e (n : ℕ) : C.homology n ≅ D.homology n :=
    asIso (HomologicalComplex.homologyMap f n)
  constructor
  · intro n
    have := hC.1 n
    exact Module.Finite.equiv (e n).toLinearEquiv
  · obtain ⟨N, hN⟩ := hC.2
    exact ⟨N, fun n hn => IsZero.of_iso (hN n hn) (e n).symm⟩

lemma finiteHomology_of_finite_simplicial (X : SSet) [X.Finite] :
    FiniteHomology (X.chainComplex (ModuleCat.of ℝ ℝ)) := by
  constructor
  · exact finiteDimensional_real_simplicial_homology X
  · obtain ⟨N, hN⟩ := real_simplicial_homology_finite_support X
    exact ⟨N, fun n hn => ModuleCat.isZero_iff_subsingleton.mpr (hN n hn)⟩

theorem property_sup_of_inf
    {L ι : Type*} [DistribLattice L] [OrderBot L] [OrderTop L]
    (P : L → Prop) (hbot : P ⊥)
    (hunion : ∀ a b, P a → P b → P (a ⊓ b) → P (a ⊔ b))
    (s : Finset ι) (f : ι → L)
    (hinter : ∀ t : Finset ι, t ⊆ s → t.Nonempty → P (t.inf f)) :
    P (s.sup f) := by
  classical
  induction s using Finset.induction_on generalizing f with
  | empty => simpa using hbot
  | @insert a s ha ih =>
    have hsingle : P (f a) := by
      simpa using hinter {a} (by simp) (by simp)
    have hrest : P (s.sup f) :=
      ih f (fun t hts ht => hinter t (hts.trans (Finset.subset_insert _ _)) ht)
    have hmeet : P (s.sup (fun i => f a ⊓ f i)) := by
      apply ih
      intro t hts ht
      have heq : t.inf (fun i => f a ⊓ f i) = (insert a t).inf f := by
        rw [Finset.inf_insert]
        change t.inf ((fun _ => f a) ⊓ f) = _
        rw [Finset.inf_inf, Finset.inf_const ht]
      rw [heq]
      exact hinter (insert a t) (Finset.insert_subset_insert a hts)
        (Finset.insert_nonempty a t)
    rw [← Finset.sup_inf_distrib_left] at hmeet
    rw [Finset.sup_insert]
    exact hunion _ _ hsingle hrest hmeet

end Problem340.FiniteGoodCover

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.HomologyZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory

namespace Problem340

theorem finiteDimensional_realSingularHomologyZero (X : Type) [TopologicalSpace X]
    [PathConnectedSpace X] : FiniteDimensional ℝ (RealSingularHomology 0 X) :=
  FiniteDimensional.of_injective (realSingularHomologyZeroEquiv X).toLinearMap
    (realSingularHomologyZeroEquiv X).injective

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.HomologyEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Problem340

theorem realSingularHomology_subsingleton_of_isEmpty
    (n : ℕ) (X : Type) [TopologicalSpace X] [IsEmpty X] :
    Subsingleton (RealSingularHomology n X) := by
  by_cases hn : n = 0
  · subst n
    let R : ModuleCat ℝ := ModuleCat.of ℝ ℝ
    let e := AlgebraicTopology.singularHomologyFunctorZeroOfTotallyDisconnectedSpace
      (ModuleCat ℝ) R (TopCat.of X)
    have hz : IsZero (∐ fun _ : X => R) := by
      apply (IsZero.iff_id_eq_zero _).mpr
      apply Sigma.hom_ext
      intro x
      exact isEmptyElim x
    exact ModuleCat.subsingleton_of_isZero (hz.of_iso e)
  · exact realSingularHomology_subsingleton_of_totallyDisconnected n hn X

theorem isZero_realSingularHomology_of_isEmpty
    (n : ℕ) (X : Type) [TopologicalSpace X] [IsEmpty X] :
    IsZero (RealSingularHomology n X) :=
  ModuleCat.isZero_iff_subsingleton.mpr
    (realSingularHomology_subsingleton_of_isEmpty n X)

theorem finiteDimensional_realSingularHomology_of_isEmpty
    (n : ℕ) (X : Type) [TopologicalSpace X] [IsEmpty X] :
    FiniteDimensional ℝ (RealSingularHomology n X) := by
  let := realSingularHomology_subsingleton_of_isEmpty n X
  infer_instance

theorem finiteDimensional_realSingularHomology_of_contractible
    (n : ℕ) (X : Type) [TopologicalSpace X] [ContractibleSpace X] :
    FiniteDimensional ℝ (RealSingularHomology n X) := by
  by_cases hn : n = 0
  · subst n
    exact finiteDimensional_realSingularHomologyZero X
  · let := realSingularHomology_subsingleton_of_contractible n hn X
    infer_instance

theorem realSingularHomology_finiteType_of_empty_or_contractible
    (X : Type) [TopologicalSpace X] (hX : IsEmpty X ∨ ContractibleSpace X) :
    (∀ n, FiniteDimensional ℝ (RealSingularHomology n X)) ∧
      (∀ n, 1 ≤ n → IsZero (RealSingularHomology n X)) := by
  rcases hX with hX | hX
  · let := hX
    exact ⟨fun n => finiteDimensional_realSingularHomology_of_isEmpty n X,
      fun n _ => isZero_realSingularHomology_of_isEmpty n X⟩
  · let := hX
    refine ⟨fun n => finiteDimensional_realSingularHomology_of_contractible n X,
      fun n hn => ?_⟩
    exact ModuleCat.isZero_iff_subsingleton.mpr
      (realSingularHomology_subsingleton_of_contractible n (by omega) X)

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SingularSmallChains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

namespace Problem340.SingularSmallChains

variable {X : Type} [TopologicalSpace X]

theorem inclusion_f_injective {ι : Type*} (U : ι → Set X) (n : ℕ) :
    Function.Injective ((inclusion U).f n).hom :=
  (ModuleCat.mono_iff_injective _).mp inferInstance

end Problem340.SingularSmallChains

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SpectralRadius
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340

theorem abs_eigenvalue_mem_homologyEigenvalueRadii
    {X : Type} [TopologicalSpace X] {f : X → X} (hf : Continuous f)
    {n : ℕ} {μ : ℝ} {v : RealSingularHomology n X}
    (hv : v ≠ 0) (heigen : realHomologyMap n f hf v = μ • v) :
    |μ| ∈ homologyEigenvalueRadii f hf := by
  refine ⟨n, μ, 0, v, 0, Or.inl hv, ?_, ?_, ?_⟩
  · simpa using heigen
  · simp
  · simp [Real.sqrt_sq_eq_abs]

theorem eigenvalue_le_totalRealHomologySpectralRadius
    {X : Type} [TopologicalSpace X] {f : X → X} (hf : Continuous f)
    (hbounded : BddAbove (homologyEigenvalueRadii f hf))
    {n : ℕ} {μ : ℝ} {v : RealSingularHomology n X}
    (hv : v ≠ 0) (heigen : realHomologyMap n f hf v = μ • v) :
    |μ| ≤ totalRealHomologySpectralRadius f hf := by
  exact le_csSup hbounded (abs_eigenvalue_mem_homologyEigenvalueRadii hf hv heigen)

theorem bddAbove_homologyEigenvalueRadii_of_finiteDimensional
    {X : Type} [TopologicalSpace X]
    [∀ n, FiniteDimensional ℝ (RealSingularHomology n X)]
    (f : X → X) (hf : Continuous f) (N : ℕ)
    (hvanish : ∀ n, N < n → Subsingleton (RealSingularHomology n X)) :
    BddAbove (homologyEigenvalueRadii f hf) :=
  bddAbove_total_pairedEigenvalue_moduli (fun n => realHomologyMap n f hf) N hvanish

theorem log_two_le_log_totalRealHomologySpectralRadius
    {X : Type} [TopologicalSpace X] {f : X → X} (hf : Continuous f)
    (hbounded : BddAbove (homologyEigenvalueRadii f hf))
    {n : ℕ} {v : RealSingularHomology n X}
    (hv : v ≠ 0) (heigen : realHomologyMap n f hf v = (2 : ℝ) • v) :
    Real.log (2 : ℝ) ≤ Real.log (totalRealHomologySpectralRadius f hf) := by
  have htwo : (2 : ℝ) ≤ totalRealHomologySpectralRadius f hf := by
    simpa using eigenvalue_le_totalRealHomologySpectralRadius hf hbounded hv heigen
  exact Real.log_le_log (by norm_num) htwo

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.FiniteCoverHomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Problem340.FiniteCoverHomology

variable {ι X : Type} [TopologicalSpace X]

theorem finiteDimensional_inSubset_homology (s : Set X) (n : ℕ)
    [FiniteDimensional ℝ (RealSingularHomology n s)] :
    FiniteDimensional ℝ ((SingularSmallChains.inSubset s : SSet).homology
      (ModuleCat.of ℝ ℝ) n : ModuleCat ℝ) :=
  Module.Finite.equiv (SingularSmallChains.subspaceHomologyIso s n).toLinearEquiv

theorem finiteHomology_goodCover_intersection
    (G : CoordinateGoodCover.GoodCover ι X) (s : Finset ι) (hs : s.Nonempty) :
    FiniteGoodCover.FiniteHomology
      ((SingularSmallChains.inSubset (⋂ i ∈ s, G.carrier i) : SSet).chainComplex
        (ModuleCat.of ℝ ℝ)) := by
  classical
  have hbase : IsEmpty ↥(⋂ i ∈ s, G.carrier i) ∨
      ContractibleSpace ↥(⋂ i ∈ s, G.carrier i) := by
    by_cases hne : (⋂ i ∈ s, G.carrier i).Nonempty
    · exact Or.inr (G.contractible s hs hne)
    · exact Or.inl ⟨fun x => hne ⟨x.val, x.property⟩⟩
  have h := realSingularHomology_finiteType_of_empty_or_contractible _ hbase
  constructor
  · intro n
    have := h.1 n
    exact finiteDimensional_inSubset_homology _ n
  · refine ⟨1, fun n hn => ?_⟩
    exact (h.2 n hn).of_iso
      (SingularSmallChains.subspaceHomologyIso (⋂ i ∈ s, G.carrier i) n).symm

theorem finiteHomology_subcomplex_bot (K : SSet.{0}) :
    FiniteGoodCover.FiniteHomology
      (((⊥ : K.Subcomplex) : SSet).chainComplex (ModuleCat.of ℝ ℝ)) := by
  have : ((⊥ : K.Subcomplex) : SSet).Finite :=
    SSet.finite_of_iso ((initialIsInitial (C := SSet)).uniqueUpToIso
      SSet.Subcomplex.isInitialBot)
  exact FiniteGoodCover.finiteHomology_of_finite_simplicial _

theorem finiteHomology_subcomplex_union {K : SSet.{0}} (A B : K.Subcomplex)
    (hA : FiniteGoodCover.FiniteHomology ((A : SSet).chainComplex (ModuleCat.of ℝ ℝ)))
    (hB : FiniteGoodCover.FiniteHomology ((B : SSet).chainComplex (ModuleCat.of ℝ ℝ)))
    (hAB : FiniteGoodCover.FiniteHomology
      (((A ⊓ B : K.Subcomplex) : SSet).chainComplex (ModuleCat.of ℝ ℝ))) :
    FiniteGoodCover.FiniteHomology
      (((A ⊔ B : K.Subcomplex) : SSet).chainComplex (ModuleCat.of ℝ ℝ)) := by
  exact FiniteGoodCover.finiteHomology_of_shortExact
    (SingularCover.unionShortComplex A B)
    (SingularCover.unionShortComplex_shortExact A B) hAB
    (FiniteGoodCover.finiteHomology_biprod hA hB)

theorem finiteHomology_subcomplex_finset_sup {K : SSet.{0}} (s : Finset ι)
    (A : ι → K.Subcomplex)
    (hinter : ∀ t : Finset ι, t ⊆ s → t.Nonempty →
      FiniteGoodCover.FiniteHomology (((t.inf A : K.Subcomplex) : SSet).chainComplex
        (ModuleCat.of ℝ ℝ))) :
    FiniteGoodCover.FiniteHomology (((s.sup A : K.Subcomplex) : SSet).chainComplex
      (ModuleCat.of ℝ ℝ)) := by
  let : DistribLattice K.Subcomplex := DistribLattice.ofInfSupLe (by
    intro B D E n σ h
    rcases h with ⟨hB, hD | hE⟩
    · exact Or.inl ⟨hB, hD⟩
    · exact Or.inr ⟨hB, hE⟩)
  refine FiniteGoodCover.property_sup_of_inf (L := K.Subcomplex)
    (fun B : K.Subcomplex => FiniteGoodCover.FiniteHomology
      ((B : SSet).chainComplex (ModuleCat.of ℝ ℝ))) ?_ ?_ s A hinter
  · exact finiteHomology_subcomplex_bot K
  · intro B D hB hD hBD
    exact finiteHomology_subcomplex_union B D hB hD hBD

private theorem finset_inf_inSubset (s : Finset ι) (U : ι → Set X) :
    s.inf (fun i => SingularSmallChains.inSubset (U i)) =
      SingularSmallChains.inSubset (⋂ i ∈ s, U i) := by
  ext n σ
  simp only [Finset.inf_eq_iInf, Subfunctor.iInf_obj,
    Set.mem_iInter, SingularSmallChains.inSubset]
  aesop

theorem finiteHomology_goodCover_small [Finite ι]
    (G : CoordinateGoodCover.GoodCover ι X) :
    FiniteGoodCover.FiniteHomology (SingularSmallChains.chains G.carrier) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have h := finiteHomology_subcomplex_finset_sup Finset.univ
    (fun i => SingularSmallChains.inSubset (G.carrier i)) (by
      intro t ht hne
      rw [finset_inf_inSubset]
      exact finiteHomology_goodCover_intersection G t hne)
  have heq : Finset.univ.sup (fun i => SingularSmallChains.inSubset (G.carrier i)) =
      SingularSmallChains.small G.carrier := by
    simp only [Finset.sup_eq_iSup, Finset.mem_univ, iSup_pos, SingularSmallChains.small]
  rw [heq] at h
  exact h

theorem finiteHomology_of_goodCover [Finite ι]
    (G : CoordinateGoodCover.GoodCover ι X)
    [QuasiIso (SingularSmallChains.inclusion G.carrier)] :
    FiniteGoodCover.FiniteHomology (realSingularChainComplex X) :=
  FiniteGoodCover.finiteHomology_of_quasiIso (SingularSmallChains.inclusion G.carrier)
    (finiteHomology_goodCover_small G)

theorem finiteDimensional_of_goodCover [Finite ι]
    (G : CoordinateGoodCover.GoodCover ι X)
    [QuasiIso (SingularSmallChains.inclusion G.carrier)] (n : ℕ) :
    FiniteDimensional ℝ (RealSingularHomology n X) :=
  (finiteHomology_of_goodCover G).1 n

theorem bddAbove_homologyEigenvalueRadii_of_goodCover [Finite ι]
    (G : CoordinateGoodCover.GoodCover ι X)
    [QuasiIso (SingularSmallChains.inclusion G.carrier)]
    (f : X → X) (hf : Continuous f) :
    BddAbove (homologyEigenvalueRadii f hf) := by
  let (n : ℕ) := finiteDimensional_of_goodCover G n
  obtain ⟨N, hN⟩ := (finiteHomology_of_goodCover G).2
  exact bddAbove_homologyEigenvalueRadii_of_finiteDimensional f hf N
    (fun n hn => ModuleCat.isZero_iff_subsingleton.mp (hN n hn.le))

end Problem340.FiniteCoverHomology

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.PolynomialSpectralBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.PolynomialSpectrum

open Polynomial

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

lemma hasPair_zero {z : ℂ} {u v : V} (huv : u ≠ 0 ∨ v ≠ 0)
    (h : HasPair (0 : Module.End ℝ V) z u v) : z = 0 := by
  rcases h with ⟨hu, hv⟩
  change 0 = z.re • u - z.im • v at hu
  change 0 = z.im • u + z.re • v at hv
  have hsu : (z.re ^ 2 + z.im ^ 2) • u = 0 := by
    calc
      (z.re ^ 2 + z.im ^ 2) • u =
          z.re • (z.re • u - z.im • v) +
            z.im • (z.im • u + z.re • v) := by module
      _ = 0 := by rw [← hu, ← hv]; simp
  have hsv : (z.re ^ 2 + z.im ^ 2) • v = 0 := by
    calc
      (z.re ^ 2 + z.im ^ 2) • v =
          -z.im • (z.re • u - z.im • v) +
            z.re • (z.im • u + z.re • v) := by module
      _ = 0 := by rw [← hu, ← hv]; simp
  have hs : z.re ^ 2 + z.im ^ 2 = 0 := by
    rcases huv with hu | hv
    · exact (smul_eq_zero.mp hsu).resolve_right hu
    · exact (smul_eq_zero.mp hsv).resolve_right hv
  apply Complex.ext <;> simp only [Complex.zero_re, Complex.zero_im]
  · nlinarith [sq_nonneg z.re, sq_nonneg z.im]
  · nlinarith [sq_nonneg z.re, sq_nonneg z.im]

section Factorization

variable {W : Type*} [AddCommGroup W] [Module ℝ W]

theorem pairRadii_comp_subset (I : W →ₗ[ℝ] V) (P : V →ₗ[ℝ] W) :
    pairRadii (I.comp P) ⊆ insert 0 (pairRadii (P.comp I)) := by
  rintro r ⟨a, b, u, v, huv, hu, hv, rfl⟩
  by_cases hP : P u ≠ 0 ∨ P v ≠ 0
  · apply Set.mem_insert_of_mem
    refine ⟨a, b, P u, P v, hP, ?_, ?_, rfl⟩
    · simpa only [LinearMap.comp_apply, map_sub, map_smul] using congrArg P hu
    · simpa only [LinearMap.comp_apply, map_add, map_smul] using congrArg P hv
  · push Not at hP
    have hz : (⟨a, b⟩ : ℂ) = 0 := by
      apply hasPair_zero huv
      constructor
      · simpa only [LinearMap.zero_apply, LinearMap.comp_apply, hP.1, map_zero] using hu
      · simpa only [LinearMap.zero_apply, LinearMap.comp_apply, hP.2, map_zero] using hv
    have ha : a = 0 := congrArg Complex.re hz
    have hb : b = 0 := congrArg Complex.im hz
    simp [ha, hb]

end Factorization

end Problem340.PolynomialSpectrum

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.HomologySpectrumFactor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340

open PolynomialSpectrum

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem homology_pairRadii_factor_subset (n : ℕ)
    (f : X → X) (i : Y → X) (p : X → Y)
    (hf : Continuous f) (hi : Continuous i) (hp : Continuous p)
    (H : ContinuousMap.Homotopy (continuousMapOf f hf)
      (continuousMapOf (i ∘ p) (hi.comp hp))) :
    pairRadii (realHomologyMap n f hf) ⊆
      insert 0 (pairRadii (realHomologyMap n (p ∘ i) (hp.comp hi))) := by
  rw [realHomologyMap_eq_of_homotopy n hf (hi.comp hp) H,
    realHomologyMap_comp n p i hp hi, realHomologyMap_comp n i p hi hp]
  exact pairRadii_comp_subset _ _

theorem bddAbove_homology_pairRadii_of_homotopy_factor
    (f : X → X) (i : Y → X) (p : X → Y)
    (hf : Continuous f) (hi : Continuous i) (hp : Continuous p)
    (H : ContinuousMap.Homotopy (continuousMapOf f hf)
      (continuousMapOf (i ∘ p) (hi.comp hp)))
    (hB : BddAbove (⋃ n, pairRadii (realHomologyMap n (p ∘ i) (hp.comp hi)))) :
    BddAbove (⋃ n, pairRadii (realHomologyMap n f hf)) := by
  apply (hB.insert 0).mono
  intro r hr
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hr
  rcases homology_pairRadii_factor_subset n f i p hf hi hp H hn with h | h
  · exact Set.mem_insert_iff.mpr (Or.inl h)
  · exact Set.mem_insert_of_mem _ (Set.mem_iUnion.mpr ⟨n, h⟩)

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.RawSpectrumFactor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340

open PolynomialSpectrum
open scoped OnePoint

theorem continuous_rawBaseProjection {q : ℕ} : Continuous (@rawBaseProjection q) :=
  continuous_fst.prodMk (continuous_fst.comp continuous_snd)

theorem continuous_rawFactorInclusion {q : ℕ} : Continuous (@rawFactorInclusion q) := by
  exact continuous_fst.prodMk
    ((continuous_snd.comp continuous_rawBaseSquare).prodMk continuous_const)

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SphereCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Metric Module Function Filter Topology
open scoped RealInnerProductSpace ContDiff OnePoint

namespace Problem340

theorem contDiff_sphereOfComplex_val {n : ℕ∞ω} :
    ContDiff ℝ n (fun z : ℂ => (sphereOfComplex z : SphereAmbient)) := by
  exact contDiff_stereoInvFunAux.comp
    ((ℝ ∙ chartNorthVector)ᗮ.subtypeL.contDiff.comp
      (chartEquatorEquiv.contDiff.comp (contDiff_id.const_smul (2 : ℝ))))

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.FiniteCoverHomologyRawBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory

namespace Problem340.FiniteCoverHomology

theorem rawBase_homologyEigenvalueRadii_bddAbove
    [QuasiIso (SingularSmallChains.inclusion CoordinateGoodCover.rawBaseGoodCover.carrier)] :
    BddAbove (homologyEigenvalueRadii rawBaseSquare continuous_rawBaseSquare) :=
  bddAbove_homologyEigenvalueRadii_of_goodCover
    CoordinateGoodCover.rawBaseGoodCover rawBaseSquare continuous_rawBaseSquare

end Problem340.FiniteCoverHomology

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.C1Coordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340

namespace HasLocalC1Extension

variable {X E F G : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]
variable {e : X → E} {f : X → F} {g : X → G}

theorem prodMk (hf : HasLocalC1Extension e f) (hg : HasLocalC1Extension e g) :
    HasLocalC1Extension e (fun x => (f x, g x)) := by
  intro x
  obtain ⟨U, hU, hxU, F, hF, hcommF⟩ := hf x
  obtain ⟨V, hV, hxV, G, hG, hcommG⟩ := hg x
  refine ⟨U ∩ V, hU.inter hV, ⟨hxU, hxV⟩, fun z => (F z, G z),
    (hF.mono Set.inter_subset_left).prodMk (hG.mono Set.inter_subset_right), ?_⟩
  intro y hy
  exact Prod.ext (hcommF y hy.1) (hcommG y hy.2)

theorem pi {ι : Type*} [Fintype ι] {F : ι → Type*}
    [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
    {f : X → ∀ i, F i} (hf : ∀ i, HasLocalC1Extension e (fun x => f x i)) :
    HasLocalC1Extension e f := by
  intro x
  choose U hU hxU F hF hcomm using fun i => hf i x
  refine ⟨⋂ i, U i, isOpen_iInter_of_finite hU, Set.mem_iInter.mpr hxU,
    fun z i => F i z, contDiffOn_pi.mpr (fun i => (hF i).mono (Set.iInter_subset U i)), ?_⟩
  intro y hy
  funext i
  exact hcomm i y (Set.mem_iInter.mp hy i)

theorem of_contDiffOn {U : Set E} (hU : IsOpen U)
    (he : ∀ x, e x ∈ U) (F : E → F) (hF : ContDiffOn ℝ 1 F U)
    (hcomm : ∀ x, f x = F (e x)) : HasLocalC1Extension e f :=
  fun x => ⟨U, hU, he x, F, hF, fun y _ => hcomm y⟩

theorem comp_contDiff (hf : HasLocalC1Extension e f) {g : F → G}
    (hg : ContDiff ℝ 1 g) : HasLocalC1Extension e (g ∘ f) := by
  intro x
  obtain ⟨U, hU, hxU, F, hF, hcomm⟩ := hf x
  refine ⟨U, hU, hxU, g ∘ F, hg.comp_contDiffOn hF, ?_⟩
  intro y hy
  change g (f y) = g (F (e y))
  rw [hcomm y hy]

end HasLocalC1Extension

theorem isC1SelfMap_iff_hasLocalC1Extension {q : ℕ}
    {f : CounterexampleManifold q → CounterexampleManifold q} :
    IsC1SelfMap q f ↔
      HasLocalC1Extension (standardEmbedding q) (standardEmbedding q ∘ f) := by
  constructor
  · exact fun hf => hf.2
  · intro hf
    exact ⟨continuous_of_local_contDiff_extension f hf, hf⟩

theorem isC1SelfMap_of_coordinate_extensions {q : ℕ}
    {f : CounterexampleManifold q → CounterexampleManifold q}
    (hclock : HasLocalC1Extension (standardEmbedding q) (fun x => (f x).1.1))
    (hsphere : ∀ i, HasLocalC1Extension (standardEmbedding q) (fun x => ((f x).2 i).1)) :
    IsC1SelfMap q f :=
  isC1SelfMap_iff_hasLocalC1Extension.mpr (hclock.prodMk (.pi hsphere))

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.ClockLocalExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ContDiff

namespace Problem340

theorem clockHomeomorph_clockLocalLift (t₀ : ℝ) (x : StandardClock) :
    clockHomeomorph ((clockLocalLift t₀ x.1 : ℝ) : AddCircle (100 : ℝ)) = x := by
  let c : Circle := circleClockHomeomorph.symm x
  let c₀ : Circle := AddCircle.toCircle (t₀ : AddCircle (100 : ℝ))
  have hc : (c : ℂ) = complexClockLinearIsometry.symm x.1 := rfl
  have hc₀ : (c₀ : ℂ) = Complex.exp ((2 * Real.pi / 100 * t₀ : ℝ) * Complex.I) := rfl
  have hlift : clockLocalLift t₀ x.1 =
      t₀ + (100 / (2 * Real.pi)) * Complex.arg ((c / c₀ : Circle) : ℂ) := by
    simp only [clockLocalLift, Circle.coe_div, hc, hc₀]
  have hangle : (2 * Real.pi / 100) *
      (t₀ + (100 / (2 * Real.pi)) * Complex.arg ((c / c₀ : Circle) : ℂ)) =
      (2 * Real.pi / 100) * t₀ + Complex.arg ((c / c₀ : Circle) : ℂ) := by
    field_simp
  rw [clockHomeomorph_apply, hlift, AddCircle.toCircle_apply_mk, hangle, Circle.exp_add,
    Circle.exp_arg]
  change circleClockHomeomorph (c₀ * (c / c₀)) = x
  simp [c, div_eq_mul_inv, mul_comm]

theorem contDiffOn_arg_slitPlane {n : ℕ∞ω} :
    ContDiffOn ℝ n Complex.arg Complex.slitPlane := by
  intro z hz
  have hlog : ContDiffAt ℝ n Complex.log z :=
    (Complex.contDiffAt_log hz).restrict_scalars ℝ
  have h := Complex.imCLM.contDiff.contDiffAt.comp z hlog
  have heq : (Complex.imCLM ∘ Complex.log) = Complex.arg := by
    funext w
    exact Complex.log_im w
  rw [heq] at h
  exact h.contDiffWithinAt

theorem clockLocalLift_extension (t₀ : ℝ) {n : ℕ∞ω} :
    ∃ U : Set ClockAmbient, IsOpen U ∧ clockParam t₀ ∈ U ∧
      ContDiffOn ℝ n (clockLocalLift t₀) U := by
  let D : ClockAmbient → ℂ := fun x => complexClockLinearIsometry.symm x /
    Complex.exp ((2 * Real.pi / 100 * t₀ : ℝ) * Complex.I)
  have hD : ContDiff ℝ n D :=
    complexClockLinearIsometry.symm.toContinuousLinearEquiv.contDiff.div_const _
  have hbase : D (clockParam t₀) = 1 := by
    simp [D, clockParam, Complex.exp_ne_zero]
  refine ⟨D ⁻¹' Complex.slitPlane, Complex.isOpen_slitPlane.preimage hD.continuous,
    ?_, ?_⟩
  · change D (clockParam t₀) ∈ Complex.slitPlane
    rw [hbase]
    exact Complex.one_mem_slitPlane
  · exact contDiffOn_const.add (contDiffOn_const.mul
      (contDiffOn_arg_slitPlane.comp hD.contDiffOn fun _ hx => hx))

theorem hasLocalC1Extension_of_clock_lift
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : StandardClock → F)
    (hf : ContDiff ℝ 1 (fun t : ℝ => f (clockHomeomorph (t : AddCircle (100 : ℝ))))) :
    HasLocalC1Extension (fun x : StandardClock => x.1) f := by
  intro x
  obtain ⟨t, rfl⟩ := clockHomeomorph.surjective x
  induction t using QuotientAddGroup.induction_on with
  | H t =>
    obtain ⟨U, hU, htU, hlocal⟩ := clockLocalLift_extension t (n := 1)
    refine ⟨U, hU, ?_,
      fun y => f (clockHomeomorph ((clockLocalLift t y : ℝ) : AddCircle (100 : ℝ))),
      hf.comp_contDiffOn hlocal, ?_⟩
    · simpa only [clockHomeomorph_coe] using htU
    · intro y _
      change f y = f (clockHomeomorph ((clockLocalLift t y.1 : ℝ) : AddCircle (100 : ℝ)))
      rw [clockHomeomorph_clockLocalLift]

theorem hasLocalC1Extension_of_clock_lift_on
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : Set E} (hV : IsOpen V) (f : StandardClock × E → F)
    (hf : ContDiffOn ℝ 1 (fun p : ℝ × E =>
      f (clockHomeomorph (p.1 : AddCircle (100 : ℝ)), p.2)) (Set.univ ×ˢ V)) :
    HasLocalC1Extension (fun x : StandardClock × V => (x.1.1, x.2.1))
      (fun x => f (x.1, x.2.1)) := by
  rintro ⟨x, a⟩
  obtain ⟨t, rfl⟩ := clockHomeomorph.surjective x
  induction t using QuotientAddGroup.induction_on with
  | H t =>
    obtain ⟨U, hU, htU, hlocal⟩ := clockLocalLift_extension t (n := 1)
    refine ⟨U ×ˢ V, hU.prod hV, ⟨?_, a.2⟩,
      fun p : ClockAmbient × E =>
        f (clockHomeomorph ((clockLocalLift t p.1 : ℝ) : AddCircle (100 : ℝ)), p.2),
      ?_, ?_⟩
    · simpa only [clockHomeomorph_coe] using htU
    · have hfst : ContDiffOn ℝ 1 (fun p : ClockAmbient × E => clockLocalLift t p.1)
          (U ×ˢ V) := hlocal.comp contDiffOn_fst (fun _ hx => hx.1)
      have hpair : ContDiffOn ℝ 1
          (fun p : ClockAmbient × E => (clockLocalLift t p.1, p.2)) (U ×ˢ V) :=
        hfst.prodMk contDiffOn_snd
      have hmaps : Set.MapsTo (fun p : ClockAmbient × E => (clockLocalLift t p.1, p.2))
          (U ×ˢ V) (Set.univ ×ˢ V) := fun _ hp => ⟨Set.mem_univ _, hp.2⟩
      convert hf.comp hpair hmaps using 1
      rfl
    · rintro ⟨y, b⟩ _
      change f (y, b.1) =
        f (clockHomeomorph ((clockLocalLift t y.1 : ℝ) : AddCircle (100 : ℝ)), b.1)
      rw [clockHomeomorph_clockLocalLift]

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.C1CoordinatePullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340

namespace HasLocalC1Extension

theorem precomp_ambient {X Y D E F : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {eX : X → E} {eY : Y → D} {f : X → F}
    (hf : HasLocalC1Extension eX f) (k : Y → X) (K : D → E)
    (hK : ContDiff ℝ 1 K) (hcomm : ∀ y, eX (k y) = K (eY y)) :
    HasLocalC1Extension eY (f ∘ k) := by
  intro y
  obtain ⟨U, hU, hyU, F, hF, hcommF⟩ := hf (k y)
  refine ⟨K ⁻¹' U, hU.preimage hK.continuous, ?_, F ∘ K,
    hF.comp hK.contDiffOn (fun _ hx => hx), ?_⟩
  · simpa only [Set.mem_preimage, ← hcomm y] using hyU
  · intro z hz
    change f (k z) = F (K (eY z))
    rw [← hcomm z]
    apply hcommF
    simpa only [Set.mem_preimage, ← hcomm z] using hz

end HasLocalC1Extension

theorem HasLocalC1Extension.clock_coordinate {q : ℕ}
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : StandardClock → F}
    (hf : HasLocalC1Extension (fun x : StandardClock => x.1) f) :
    HasLocalC1Extension (standardEmbedding q)
      (fun x : CounterexampleManifold q => f x.1) :=
  hf.precomp_ambient Prod.fst Prod.fst contDiff_fst (fun _ => rfl)

theorem HasLocalC1Extension.sphere_coordinate {q : ℕ}
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : StandardSphere2 → F}
    (hf : HasLocalC1Extension (fun x : StandardSphere2 => x.1) f)
    (i : Fin (q + 1)) :
    HasLocalC1Extension (standardEmbedding q)
      (fun x : CounterexampleManifold q => f (x.2 i)) :=
  hf.precomp_ambient (fun x : CounterexampleManifold q => x.2 i)
    (fun x : CounterexampleAmbient q => x.2 i)
    ((contDiff_apply ℝ SphereAmbient i).comp contDiff_snd) (fun _ => rfl)

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.ClockRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.Clock

lemma contDiff_rotate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ∞} {x : E → ClockAmbient} {a : E → ℝ}
    (hx : ContDiff ℝ n x) (ha : ContDiff ℝ n a) :
    ContDiff ℝ n (fun y => rotate (x y) (a y)) := by
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i
  · exact (((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contDiff.comp hx).mul ha.cos).sub
      (((EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contDiff.comp hx).mul ha.sin)
  · exact (((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contDiff.comp hx).mul ha.sin).add
      (((EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contDiff.comp hx).mul ha.cos)

lemma rotate_parametrization (t h : ℝ) :
    rotate (parametrization t) (2 * Real.pi * h / 100) = parametrization (t + h) := by
  ext i
  fin_cases i
  · change Real.cos (2 * Real.pi * t / 100) * Real.cos (2 * Real.pi * h / 100) -
        Real.sin (2 * Real.pi * t / 100) * Real.sin (2 * Real.pi * h / 100) =
      Real.cos (2 * Real.pi * (t + h) / 100)
    rw [show 2 * Real.pi * (t + h) / 100 =
        2 * Real.pi * t / 100 + 2 * Real.pi * h / 100 by ring, Real.cos_add]
  · change Real.cos (2 * Real.pi * t / 100) * Real.sin (2 * Real.pi * h / 100) +
        Real.sin (2 * Real.pi * t / 100) * Real.cos (2 * Real.pi * h / 100) =
      Real.sin (2 * Real.pi * (t + h) / 100)
    rw [show 2 * Real.pi * (t + h) / 100 =
        2 * Real.pi * t / 100 + 2 * Real.pi * h / 100 by ring, Real.sin_add]
    ring

lemma contDiff_ambientIncrement {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ∞} {x : E → ClockAmbient} {e : E → ℝ}
    (hx : ContDiff ℝ n x) (he : ContDiff ℝ n e) :
    ContDiff ℝ n (fun y => ambientIncrement (x y) (e y)) := by
  exact (contDiff_ambientBarrier.comp hx).add
    ((contDiff_const.sub (contDiff_ambientBarrier.comp hx)).mul he)

lemma ambientIncrement_parametrization (t e : ℝ) :
    ambientIncrement (parametrization t) e = increment t e := by
  simp only [ambientIncrement, increment,
    ambientBarrier_on_circle t (parametrization t) (parametrization_zero t)]

lemma contDiff_ambientUpdate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ∞} {x : E → ClockAmbient} {e : E → ℝ}
    (hx : ContDiff ℝ n x) (he : ContDiff ℝ n e) :
    ContDiff ℝ n (fun y => ambientUpdate (x y) (e y)) := by
  apply contDiff_rotate hx
  exact (contDiff_const.mul (contDiff_ambientIncrement hx he)).div_const 100

lemma ambientUpdate_parametrization (t e : ℝ) :
    ambientUpdate (parametrization t) e = parametrization (t + increment t e) := by
  rw [ambientUpdate, ambientIncrement_parametrization, rotate_parametrization]

end Problem340.Clock

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.ClockLiftBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.Clock

lemma clockHomeomorph_val_real (t : ℝ) :
    (ClockModel.clockHomeomorph (t : AddCircle (100 : ℝ))).val = parametrization t := by
  ext i
  fin_cases i
  · change (ClockModel.clockHomeomorph (t : AddCircle (100 : ℝ))).val 0 =
      Real.cos (2 * Real.pi * t / 100)
    simp [ClockModel.clockHomeomorph, Homeomorph.trans_apply,
      AddCircle.homeomorphCircle_apply,
      AddCircle.toCircle_apply_mk, Circle.coe_exp, Complex.exp_re]
    congr 1
    ring
  · change (ClockModel.clockHomeomorph (t : AddCircle (100 : ℝ))).val 1 =
      Real.sin (2 * Real.pi * t / 100)
    simp [ClockModel.clockHomeomorph, Homeomorph.trans_apply,
      AddCircle.homeomorphCircle_apply,
      AddCircle.toCircle_apply_mk, Circle.coe_exp, Complex.exp_im]
    congr 1
    ring

lemma update_clockHomeomorph_real (t e : ℝ) :
    update (ClockModel.clockHomeomorph (t : AddCircle (100 : ℝ))) e =
      ClockModel.clockHomeomorph ((t + increment t e : ℝ) : AddCircle (100 : ℝ)) := by
  apply Subtype.ext
  change ambientUpdate _ e = _
  rw [clockHomeomorph_val_real, clockHomeomorph_val_real, ambientUpdate_parametrization]

lemma update_clockHomeomorph (t : AddCircle (100 : ℝ)) (e : ℝ) :
    update (ClockModel.clockHomeomorph t) e =
      ClockModel.clockHomeomorph
        (t + (ambientIncrement (ClockModel.clockHomeomorph t).val e : ℝ)) := by
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective t
  have hi : ambientIncrement (ClockModel.clockHomeomorph (t : AddCircle (100 : ℝ))).val e =
      increment t e := by
    rw [clockHomeomorph_val_real]
    exact ambientIncrement_parametrization t e
  rw [hi]
  exact update_clockHomeomorph_real t e

end Problem340.Clock

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.ReadoutCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Problem340

theorem preparationCoeff_nonneg (t : ℝ) : 0 ≤ preparationCoeff t :=
  preparationBump.nonneg

theorem preparationCoeff_le_one (t : ℝ) : preparationCoeff t ≤ 1 :=
  preparationBump.le_one

theorem readoutCoeff_hasCompactSupport (i : Fin 3) :
    HasCompactSupport (readoutCoeff i) := (readoutBump i).hasCompactSupport

theorem preparationCoeff_hasCompactSupport : HasCompactSupport preparationCoeff :=
  preparationBump.hasCompactSupport

theorem exists_readoutCoeff_fderiv_bound :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ i : Fin 3, ∀ t : ℝ, ‖fderiv ℝ (readoutCoeff i) t‖ ≤ C := by
  have hlocal : ∀ i : Fin 3, ∃ C : ℝ, ∀ t : ℝ, ‖fderiv ℝ (readoutCoeff i) t‖ ≤ C := by
    intro i
    exact ((readoutCoeff_hasCompactSupport i).fderiv (𝕜 := ℝ)).exists_bound_of_continuous
      ((readoutCoeff_contDiff i (n := 1)).continuous_fderiv (by norm_num))
  choose C hC using hlocal
  refine ⟨1 + ∑ i : Fin 3, |C i|, ?_, ?_⟩
  · have hs : 0 ≤ ∑ i : Fin 3, |C i| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    linarith
  · intro i t
    have hi : |C i| ≤ ∑ j : Fin 3, |C j| :=
      Finset.single_le_sum (f := fun j : Fin 3 => |C j|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    exact (hC i t).trans ((le_abs_self (C i)).trans (by linarith))

theorem exists_preparationCoeff_fderiv_bound :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ t : ℝ, ‖fderiv ℝ preparationCoeff t‖ ≤ C := by
  obtain ⟨C, hC⟩ := (preparationCoeff_hasCompactSupport.fderiv (𝕜 := ℝ)).exists_bound_of_continuous
    ((preparationCoeff_contDiff (n := 1)).continuous_fderiv (by norm_num))
  refine ⟨1 + |C|, le_add_of_nonneg_right (abs_nonneg C), fun t => ?_⟩
  exact (hC t).trans ((le_abs_self C).trans (by linarith))

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.Map
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped OnePoint

namespace Problem340.Construction

attribute [local instance] OAI.Problem340.Construction.instFactLtRealOfNat_solutions
theorem rawMap_register_ne_infty (D : SphereData) (x : RawManifold) (i : Fin 3) :
    (rawMap D x).2.2 i ≠ ∞ := OnePoint.coe_ne_infty _

theorem rawMap_not_surjective (D : SphereData) : ¬ Function.Surjective (rawMap D) := by
  intro h
  obtain ⟨x, hx⟩ := h (0, ∞, fun _ => ∞)
  have heq := congrArg (fun y : RawManifold => y.2.2 (0 : Fin 3)) hx
  exact rawMap_register_ne_infty D x 0 heq

theorem rawMap_not_bijective (D : SphereData) : ¬ Function.Bijective (rawMap D) :=
  fun h => rawMap_not_surjective D h.2

end Problem340.Construction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SphereCutoffsAffine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter Topology

namespace Problem340.SphereCutoffs

theorem clockGate_eq_affineClockGate {x : StandardSphere2} {z : ℂ}
    (hh : x.1 2 = affineHeight z) : clockGate x = affineClockGate z := by
  simp only [clockGate, clockGateAmbient, affineClockGate, hh]

end Problem340.SphereCutoffs

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.MapData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped OnePoint

namespace Problem340.Construction

local instance instFactLtRealOfNat_solutions_1_ree851b_1 : Fact ((0 : ℝ) < 100) := ⟨by norm_num⟩
theorem concreteMap_not_bijective (L : ℝ) (hL : 2 < L) :
    ¬ Function.Bijective (concreteMap L hL) :=
  rawMap_not_bijective _

end Problem340.Construction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.MapClockComponent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped OnePoint

namespace Problem340.Construction

lemma onePointClockGate_eq_ambient (z : Sphere) :
    SphereCutoffs.onePointClockGate z =
      SphereCutoffs.clockGateAmbient (complexSphereHomeomorph z).val := by
  induction z using OnePoint.rec with
  | infty =>
      symm
      apply SphereCutoffs.clockGateAmbient_eq_one
      norm_num [complexSphereHomeomorph_infty, chartNorthPole, chartNorthVector]
  | coe z =>
      change SphereCutoffs.affineClockGate z = SphereCutoffs.clockGate (sphereOfComplex z)
      symm
      apply SphereCutoffs.clockGate_eq_affineClockGate
      exact sphereOfComplex_val_two z

lemma concrete_clockIncrement_eq_ambient (L : ℝ) (hL : 2 < L)
    (t : AddCircle (100 : ℝ)) (z : Sphere) :
    clockIncrement (concreteData L hL) t z =
      Clock.ambientIncrement (ClockModel.clockHomeomorph t).val
        (SphereCutoffs.clockGateAmbient (complexSphereHomeomorph z).val) := by
  obtain ⟨r, hr, rfl⟩ := AddCircle.eq_coe_Ico t
  rw [clockIncrement, AddCircle.liftIco_zero_coe_apply hr,
    Clock.clockHomeomorph_val_real, Clock.ambientIncrement_parametrization]
  change Clock.increment r (SphereCutoffs.onePointClockGate z) = _
  rw [onePointClockGate_eq_ambient]

lemma concreteMap_clock_eq_update (L : ℝ) (hL : 2 < L) (x : RawManifold) :
    ClockModel.clockHomeomorph (concreteMap L hL x).1 =
      Clock.update (ClockModel.clockHomeomorph x.1)
        (SphereCutoffs.clockGateAmbient (complexSphereHomeomorph x.2.1).val) := by
  change ClockModel.clockHomeomorph
    (x.1 + (clockIncrement (concreteData L hL) x.1 x.2.1 : ℝ)) = _
  rw [concrete_clockIncrement_eq_ambient]
  exact (Clock.update_clockHomeomorph _ _).symm

lemma contDiff_concreteClockAmbient {n : ℕ∞} :
    ContDiff ℝ n concreteClockAmbient := by
  apply Clock.contDiff_ambientUpdate contDiff_fst
  exact SphereCutoffs.contDiff_clockGateAmbient.comp
    ((contDiff_apply ℝ SphereAmbient (0 : Fin 4)).comp contDiff_snd)

lemma transported_concreteMap_clock_ambient (L : ℝ) (hL : 2 < L)
    (x : CounterexampleManifold 3) :
    ((ClockModel.productHomeomorph 3 complexSphereHomeomorph)
      (concreteMap L hL ((ClockModel.productHomeomorph 3 complexSphereHomeomorph).symm x))).1.val =
      concreteClockAmbient (standardEmbedding 3 x) := by
  let e := ClockModel.productHomeomorph 3 complexSphereHomeomorph
  obtain ⟨y, rfl⟩ := e.surjective x
  change (e (concreteMap L hL (e.symm (e y)))).1.val = _
  rw [e.symm_apply_apply]
  change (ClockModel.clockHomeomorph (concreteMap L hL y).1).val = _
  rw [concreteMap_clock_eq_update]
  rfl

end Problem340.Construction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.Conjugacy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340

theorem bijective_conjugateMap {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y)
    {f : X → X} (hf : Function.Bijective f) : Function.Bijective (conjugateMap e f) :=
  e.bijective.comp (hf.comp e.symm.bijective)

@[simp] theorem bijective_conjugateMap_iff {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) (f : X → X) :
    Function.Bijective (conjugateMap e f) ↔ Function.Bijective f := by
  constructor
  · intro h
    simpa using bijective_conjugateMap e.symm h
  · exact bijective_conjugateMap e

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.C1Conjugacy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340

theorem HasLocalC1Extension.comp
    {X Y E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {eX : X → E} {eY : Y → F} {f : X → Y} {g : Y → G}
    (hg : HasLocalC1Extension eY g)
    (hf : HasLocalC1Extension eX (eY ∘ f)) :
    HasLocalC1Extension eX (g ∘ f) := by
  intro x
  obtain ⟨U, hU, hxU, F, hF, hFe⟩ := hf x
  simp only [Function.comp_apply] at hFe
  obtain ⟨V, hV, hfxV, G, hG, hGe⟩ := hg (f x)
  refine ⟨U ∩ F ⁻¹' V, hF.continuousOn.isOpen_inter_preimage hU hV, ?_,
    G ∘ F, hG.comp_inter hF, ?_⟩
  · refine ⟨hxU, ?_⟩
    change F (eX x) ∈ V
    rw [← hFe x hxU]
    exact hfxV
  · intro y hy
    change g (f y) = G (F (eX y))
    rw [hGe (f y) (by rw [hFe y hy.1]; exact hy.2), hFe y hy.1]

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.HomologyConjugacy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem realHomologyMap_conjugateMap_intertwines (n : ℕ) (e : X ≃ₜ Y)
    {f : X → X} (hf : Continuous f) :
    (realHomologyMap n (conjugateMap e f) (continuous_conjugateMap e hf)).comp
        (realHomologyMap n e e.continuous) =
      (realHomologyMap n e e.continuous).comp (realHomologyMap n f hf) := by
  rw [← realHomologyMap_comp, ← realHomologyMap_comp]
  congr 1
  funext x
  simp

theorem realHomologyEquiv_conjugateMap (n : ℕ) (e : X ≃ₜ Y)
    {f : X → X} (hf : Continuous f) (v : RealSingularHomology n X) :
    realHomologyMap n (conjugateMap e f) (continuous_conjugateMap e hf)
        (realHomologyEquiv n e v) =
      realHomologyEquiv n e (realHomologyMap n f hf v) := by
  exact congrArg (fun A : RealSingularHomology n X →ₗ[ℝ] RealSingularHomology n Y => A v)
    (realHomologyMap_conjugateMap_intertwines n e hf)

theorem realHomologyMap_eigenvector_conjugateMap (n : ℕ) (e : X ≃ₜ Y)
    {f : X → X} (hf : Continuous f) (c : ℝ)
    (v : RealSingularHomology n X) (hv : v ≠ 0)
    (heig : realHomologyMap n f hf v = c • v) :
    ∃ w : RealSingularHomology n Y, w ≠ 0 ∧
      realHomologyMap n (conjugateMap e f) (continuous_conjugateMap e hf) w = c • w := by
  refine ⟨realHomologyEquiv n e v, ?_, ?_⟩
  · exact (map_ne_zero_iff (realHomologyEquiv n e) (realHomologyEquiv n e).injective).2 hv
  · rw [realHomologyEquiv_conjugateMap n e hf, heig, map_smul]

theorem realHomologyMap_complexPair_conjugateMap (n : ℕ) (e : X ≃ₜ Y)
    {f : X → X} (hf : Continuous f) (a b : ℝ)
    (u v : RealSingularHomology n X) (huv : u ≠ 0 ∨ v ≠ 0)
    (hu : realHomologyMap n f hf u = a • u - b • v)
    (hv : realHomologyMap n f hf v = b • u + a • v) :
    ∃ u' v' : RealSingularHomology n Y,
      (u' ≠ 0 ∨ v' ≠ 0) ∧
      realHomologyMap n (conjugateMap e f) (continuous_conjugateMap e hf) u' =
        a • u' - b • v' ∧
      realHomologyMap n (conjugateMap e f) (continuous_conjugateMap e hf) v' =
        b • u' + a • v' := by
  refine ⟨realHomologyEquiv n e u, realHomologyEquiv n e v, ?_, ?_, ?_⟩
  · simpa only [map_ne_zero_iff (realHomologyEquiv n e)
      (realHomologyEquiv n e).injective] using huv
  · rw [realHomologyEquiv_conjugateMap n e hf, hu, map_sub, map_smul, map_smul]
  · rw [realHomologyEquiv_conjugateMap n e hf, hv, map_add, map_smul, map_smul]

theorem totalRealHomologySpectralRadius_conjugateMap (e : X ≃ₜ Y)
    {f : X → X} (hf : Continuous f) :
    totalRealHomologySpectralRadius (conjugateMap e f) (continuous_conjugateMap e hf) =
      totalRealHomologySpectralRadius f hf := by
  unfold totalRealHomologySpectralRadius
  congr 1
  ext r
  constructor
  · rintro ⟨n, a, b, u, v, huv, hu, hv, hr⟩
    obtain ⟨u', v', huv', hu', hv'⟩ := realHomologyMap_complexPair_conjugateMap
      n e.symm (continuous_conjugateMap e hf) a b u v huv hu hv
    exact ⟨n, a, b, u', v', huv', by simpa using hu', by simpa using hv', hr⟩
  · rintro ⟨n, a, b, u, v, huv, hu, hv, hr⟩
    obtain ⟨u', v', huv', hu', hv'⟩ := realHomologyMap_complexPair_conjugateMap
      n e hf a b u v huv hu hv
    exact ⟨n, a, b, u', v', huv', hu', hv', hr⟩

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.RealizedConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped OnePoint

namespace Problem340.Construction

attribute [local instance] OAI.Problem340.Construction.instFactLtRealOfNat_solutions_2
theorem realizedMap_not_bijective (L : ℝ) (hL : 2 < L) :
    ¬ Function.Bijective (realizedMap L hL) := by
  simpa only [realizedMap, bijective_conjugateMap_iff] using concreteMap_not_bijective L hL

theorem realizedMap_eigenvector (L : ℝ) (hL : 2 < L)
    (hf : Continuous (concreteMap L hL)) (n : ℕ) (c : ℝ)
    (v : RealSingularHomology n RawManifold) (hv : v ≠ 0)
    (heig : realHomologyMap n (concreteMap L hL) hf v = c • v) :
    ∃ w : RealSingularHomology n (CounterexampleManifold 3), w ≠ 0 ∧
      realHomologyMap n (realizedMap L hL) (continuous_realizedMap L hL hf) w = c • w :=
  realHomologyMap_eigenvector_conjugateMap n modelHomeomorph hf c v hv heig

theorem totalRealHomologySpectralRadius_realizedMap (L : ℝ) (hL : 2 < L)
    (hf : Continuous (concreteMap L hL)) :
    totalRealHomologySpectralRadius (realizedMap L hL) (continuous_realizedMap L hL hf) =
      totalRealHomologySpectralRadius (concreteMap L hL) hf :=
  totalRealHomologySpectralRadius_conjugateMap modelHomeomorph hf

end Problem340.Construction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.MapC1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.Construction

theorem realizedMap_clock_hasLocalC1Extension (L : ℝ) (hL : 2 < L) :
    HasLocalC1Extension (standardEmbedding 3)
      (fun x => (realizedMap L hL x).1.1) := by
  apply HasLocalC1Extension.of_contDiffOn isOpen_univ (fun _ => Set.mem_univ _)
    concreteClockAmbient contDiff_concreteClockAmbient.contDiffOn
  exact transported_concreteMap_clock_ambient L hL

theorem isC1SelfMap_realizedMap_of_sphere_components (L : ℝ) (hL : 2 < L)
    (hmain : HasLocalC1Extension (standardEmbedding 3)
      (fun x => ((realizedMap L hL x).2 0).1))
    (hregister : ∀ i : Fin 3, HasLocalC1Extension (standardEmbedding 3)
      (fun x => ((realizedMap L hL x).2 i.succ).1)) :
    IsC1SelfMap 3 (realizedMap L hL) := by
  apply isC1SelfMap_of_coordinate_extensions
    (realizedMap_clock_hasLocalC1Extension L hL)
  intro i
  exact Fin.cases hmain hregister i

end Problem340.Construction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.ClockPeriodization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Filter Function
open scoped Topology ContDiff

namespace Problem340.ClockPeriodization

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem contDiff_tsum_of_locallyFinite {ι : Type*} {f : ι → E → F} {n : ℕ∞ω}
    (hf : ∀ i, ContDiff ℝ n (f i))
    (hl : LocallyFinite (fun i => support (f i))) :
    ContDiff ℝ n (fun x => ∑' i, f i x) := by
  have heq : (fun x => ∑' i, f i x) = (fun x => ∑ᶠ i, f i x) := by
    funext x
    exact tsum_eq_finsum (hl.point_finite x)
  rw [heq]
  exact contMDiff_iff_contDiff.mp (contMDiff_finsum
    (fun i => contMDiff_iff_contDiff.mpr (hf i)) hl)

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in

theorem locallyFinite_translates {P a b : ℝ} (hP : 0 < P) {f : ℝ × E → F}
    (hsupport : ∀ x, f x ≠ 0 → x.1 ∈ Icc a b) :
    LocallyFinite (fun k : ℤ => support (fun x : ℝ × E =>
      f (x.1 - (k : ℝ) * P, x.2))) := by
  refine ((locallyFinite_clockIntervals hP a b).preimage_continuous continuous_fst).subset ?_
  intro k x hx
  have h := hsupport (x.1 - (k : ℝ) * P, x.2) hx
  change (k : ℝ) * P + a ≤ x.1 ∧ x.1 ≤ (k : ℝ) * P + b
  constructor <;> linarith [h.1, h.2]

theorem contDiff_periodize {P a b : ℝ} {n : ℕ∞ω} (hP : 0 < P)
    {f : ℝ × E → F} (hf : ContDiff ℝ n f)
    (hsupport : ∀ x, f x ≠ 0 → x.1 ∈ Icc a b) :
    ContDiff ℝ n (periodize P f) := by
  apply contDiff_tsum_of_locallyFinite
  · intro k
    exact hf.comp ((contDiff_fst.sub contDiff_const).prodMk contDiff_snd)
  · exact locallyFinite_translates hP hsupport

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℝ F] in

theorem periodize_add_period (P : ℝ) (f : ℝ × E → F) (t : ℝ) (x : E) :
    periodize P f (t + P, x) = periodize P f (t, x) := by
  unfold periodize
  calc
    (∑' k : ℤ, f (t + P - (k : ℝ) * P, x)) =
        ∑' k : ℤ, f (t - ((k + -1 : ℤ) : ℝ) * P, x) := by
      apply tsum_congr
      intro k
      apply congrArg (fun r : ℝ => f (r, x))
      push_cast
      ring
    _ = ∑' k : ℤ, f (t - (k : ℝ) * P, x) :=
      (Equiv.addRight (-1 : ℤ)).tsum_eq (fun k : ℤ => f (t - (k : ℝ) * P, x))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℝ F] in

theorem periodize_eq_on_fundamental {P : ℝ} (hP : 0 < P) {f : ℝ × E → F}
    (hsupport : ∀ x, f x ≠ 0 → x.1 ∈ Ioo 0 P)
    {t : ℝ} (ht : t ∈ Icc 0 P) (x : E) :
    periodize P f (t, x) = f (t, x) := by
  unfold periodize
  rw [tsum_eq_single (0 : ℤ)]
  · simp
  · intro k hk
    by_contra hne
    have h := hsupport (t - (k : ℝ) * P, x) hne
    rcases lt_or_gt_of_ne hk with hkn | hkp
    · have hk1 : k ≤ -1 := by omega
      have hk1' : (k : ℝ) ≤ -1 := by exact_mod_cast hk1
      nlinarith [h.2, ht.1]
    · have hk1 : 1 ≤ k := by omega
      have hk1' : 1 ≤ (k : ℝ) := by exact_mod_cast hk1
      nlinarith [h.1, ht.2]

end Problem340.ClockPeriodization

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.ClockQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Filter Function
open scoped Topology

namespace Problem340
namespace ClockQuotient

variable {E F : Type*}

lemma periodize_eq_tsum [TopologicalSpace E]
    [AddCommMonoid F] [TopologicalSpace F]
    {P a b : ℝ} {f : ℝ × E → F}
    (hP : 0 < P) (hsupp : ∀ x, f x ≠ 0 → x.1 ∈ Icc a b) (x : ℝ × E) :
    periodize P f x = ∑' k : ℤ, f (x.1 - (k : ℝ) * P, x.2) := by
  exact (tsum_eq_finsum
    ((locallyFinite_translated_supports hP hsupp).point_finite x)).symm

end ClockQuotient
end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.ClockPeriodizationCompatibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Function
open scoped ContDiff

namespace Problem340.ClockQuotient

variable {E F : Type*}

theorem periodize_eq_clockPeriodization [TopologicalSpace E] [NormedAddCommGroup F]
    {P a b : ℝ} {f : ℝ × E → F} (hP : 0 < P)
    (hsupp : ∀ x, f x ≠ 0 → x.1 ∈ Icc a b) :
    periodize P f = ClockPeriodization.periodize P f := by
  funext x
  exact periodize_eq_tsum hP hsupp x

end Problem340.ClockQuotient

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.ClockPeriodizationLocal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Function
open scoped ContDiff

namespace Problem340.ClockPeriodization

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem contDiffOn_tsum_of_locallyFinite {ι : Type*} {f : ι → E → F}
    {n : ℕ∞ω} {s : Set E} (hf : ∀ i, ContDiffOn ℝ n (f i) s)
    (hl : LocallyFinite (fun i => support (f i))) :
    ContDiffOn ℝ n (fun x => ∑' i, f i x) s := by
  have heq : (fun x => ∑' i, f i x) = (fun x => ∑ᶠ i, f i x) := by
    funext x
    exact tsum_eq_finsum (hl.point_finite x)
  rw [heq]
  exact contMDiffOn_iff_contDiffOn.mp (contMDiffOn_finsum hl
    (fun i => contMDiffOn_iff_contDiffOn.mpr (hf i)))

theorem contDiffOn_periodize {P a b : ℝ} {n : ℕ∞ω} {U : Set E}
    (hP : 0 < P) {f : ℝ × E → F}
    (hf : ContDiffOn ℝ n f (univ ×ˢ U))
    (hsupport : ∀ x, f x ≠ 0 → x.1 ∈ Icc a b) :
    ContDiffOn ℝ n (periodize P f) (univ ×ˢ U) := by
  apply contDiffOn_tsum_of_locallyFinite
  · intro k
    exact hf.comp ((contDiff_fst.sub contDiff_const).prodMk contDiff_snd).contDiffOn
      (fun x hx => ⟨mem_univ _, hx.2⟩)
  · exact locallyFinite_translates hP hsupport

end Problem340.ClockPeriodization

namespace Problem340.ClockQuotient

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem contDiffOn_periodize {P a b : ℝ} {n : ℕ∞ω} {U : Set E}
    (hP : 0 < P) {f : ℝ × E → F}
    (hf : ContDiffOn ℝ n f (univ ×ˢ U))
    (hsupport : ∀ x, f x ≠ 0 → x.1 ∈ Icc a b) :
    ContDiffOn ℝ n (periodize P f) (univ ×ˢ U) := by
  rw [periodize_eq_clockPeriodization hP hsupport]
  exact ClockPeriodization.contDiffOn_periodize hP hf hsupport

end Problem340.ClockQuotient

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.ClockQuotientC1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Function
open scoped ContDiff

namespace Problem340.ClockQuotient

attribute [local instance] OAI.Problem340.ClockQuotient.instFactLtRealOfNat_solutions
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℝ F] in

theorem liftIco_clockHomeomorph_strip {f : ℝ × E → F}
    (hs : ∀ x, f x ≠ 0 → x.1 ∈ Ioo 0 100) (p : ℝ × E) :
    AddCircle.liftIco (100 : ℝ) 0 (fun t => f (t, p.2))
      (clockHomeomorph.symm (clockHomeomorph (p.1 : AddCircle (100 : ℝ)))) =
        periodize 100 f p := by
  rw [clockHomeomorph.symm_apply_apply]
  exact (liftPeriodize_eq_liftIco hs ((p.1 : AddCircle (100 : ℝ)), p.2)).symm.trans
    (liftPeriodize_coe 100 f p.1 p.2)

theorem hasLocalC1Extension_liftIco_of_strip_support_on {V : Set E} (hV : IsOpen V)
    {f : ℝ × E → F} (hf : ContDiffOn ℝ 1 f (univ ×ˢ V))
    (hs : ∀ x, f x ≠ 0 → x.1 ∈ Ioo 0 100) :
    HasLocalC1Extension (fun x : StandardClock × V => (x.1.1, x.2.1))
      (fun x => AddCircle.liftIco (100 : ℝ) 0 (fun t => f (t, x.2.1))
        (clockHomeomorph.symm x.1)) := by
  refine hasLocalC1Extension_of_clock_lift_on hV
    (fun x : StandardClock × E => AddCircle.liftIco (100 : ℝ) 0
      (fun t => f (t, x.2)) (clockHomeomorph.symm x.1)) ?_
  have hs' : ∀ x, f x ≠ 0 → x.1 ∈ Icc 0 100 :=
    fun x hx => ⟨(hs x hx).1.le, (hs x hx).2.le⟩
  simpa only [liftIco_clockHomeomorph_strip hs] using
    contDiffOn_periodize (by norm_num : (0 : ℝ) < 100) hf hs'

end Problem340.ClockQuotient

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.InputSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340

open Set
open scoped ContDiff

variable {ι E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {f : ι → E → F} {u : ι → ℝ} {s : Set E} {x₀ : E}

theorem hasFDerivAt_tsum_on_open
    (hs : IsOpen s) (hf : ∀ i, ContDiffOn ℝ 1 (f i) s)
    (hu : Summable u)
    (hbound : ∀ i x, x ∈ s → ‖fderiv ℝ (f i) x‖ ≤ u i)
    (hpoint : ∀ x ∈ s, Summable (fun i => f i x))
    {x : E} (hx : x ∈ s) :
    HasFDerivAt (fun y => ∑' i, f i y)
      (∑' i, fderiv ℝ (f i) x) x := by
  classical
  apply hasFDerivAt_of_tendstoUniformlyOn hs (tendstoUniformlyOn_tsum hu hbound)
    (fun t y hy => ?_) (fun y hy => (hpoint y hy).hasSum) hx
  exact HasFDerivAt.fun_sum fun i _ =>
    ((hf i).differentiableOn_one y hy).differentiableAt
      (hs.mem_nhds hy) |>.hasFDerivAt

theorem contDiffOn_tsum_on_open
    (hs : IsOpen s) (hf : ∀ i, ContDiffOn ℝ 1 (f i) s)
    (hu : Summable u)
    (hbound : ∀ i x, x ∈ s → ‖fderiv ℝ (f i) x‖ ≤ u i)
    (hpoint : ∀ x ∈ s, Summable (fun i => f i x)) :
    ContDiffOn ℝ 1 (fun x => ∑' i, f i x) s := by
  rw [show (1 : ℕ∞ω) = 0 + 1 from rfl,
    contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hs.uniqueDiffOn]
  refine ⟨by simp, (fun x => ∑' i, fderiv ℝ (f i) x), ?_, ?_⟩
  · apply contDiffOn_zero.mpr
    exact continuousOn_tsum
      (fun i => (hf i).continuousOn_fderiv_of_isOpen hs (by rfl)) hu hbound
  · intro x hx
    exact (hasFDerivAt_tsum_on_open hs hf hu hbound hpoint hx).hasFDerivWithinAt

theorem contDiffOn_tsum_of_norm_add_fderiv_bound
    (hs : IsOpen s) (hf : ∀ i, ContDiffOn ℝ 1 (f i) s)
    (hu : Summable u)
    (hbound : ∀ i x, x ∈ s → ‖f i x‖ + ‖fderiv ℝ (f i) x‖ ≤ u i) :
    ContDiffOn ℝ 1 (fun x => ∑' i, f i x) s := by
  apply contDiffOn_tsum_on_open hs hf hu
  · intro i x hx
    exact le_trans (le_add_of_nonneg_left (norm_nonneg _)) (hbound i x hx)
  · intro x hx
    exact Summable.of_norm_bounded hu fun i =>
      le_trans (le_add_of_nonneg_right (norm_nonneg _)) (hbound i x hx)

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.PredictionSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340

theorem summable_predictionMajorant {C B L : ℝ}
    (hB : 0 ≤ B) (hBL : B < L) (hL : 2 < L) :
    Summable (predictionMajorant C B L) := by
  have hL0 : 0 < L := by linarith
  have hInv : L⁻¹ < 1 := by
    rw [inv_lt_one₀ hL0]
    linarith
  have hRatioB : B * L⁻¹ < 1 := by
    rw [← div_eq_mul_inv, div_lt_one hL0]
    exact hBL
  have hRatio2 : 2 * L⁻¹ < 1 := by
    rw [← div_eq_mul_inv, div_lt_one hL0]
    exact hL
  have h₀ : Summable (fun n : ℕ => (L⁻¹) ^ n) :=
    summable_geometric_of_lt_one (inv_nonneg.mpr hL0.le) hInv
  have h₁ : Summable (fun n : ℕ => (B * L⁻¹) ^ n) :=
    summable_geometric_of_lt_one (mul_nonneg hB (inv_nonneg.mpr hL0.le)) hRatioB
  have h₂ : Summable (fun n : ℕ => (2 * L⁻¹) ^ n) :=
    summable_geometric_of_lt_one (by positivity) hRatio2
  have hs := ((h₀.add (h₁.mul_left B)).add (h₂.mul_left 4)).mul_left C
  apply hs.congr
  intro n
  simp only [predictionMajorant, mul_pow, pow_add, pow_one, pow_two]
  ring

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.PredictionInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340

theorem norm_fderiv_smul_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {a : E → ℝ} {v : E → F} {x : E}
    (ha : DifferentiableAt ℝ a x) (hv : DifferentiableAt ℝ v x) :
    ‖fderiv ℝ (fun y => a y • v y) x‖ ≤
      ‖a x‖ * ‖fderiv ℝ v x‖ + ‖fderiv ℝ a x‖ * ‖v x‖ := by
  rw [fderiv_fun_smul ha hv]
  exact (norm_add_le _ _).trans_eq (by
    rw [norm_smul, ContinuousLinearMap.norm_smulRight_apply])

theorem norm_add_fderiv_predictionTerm_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {a b : E → ℝ} {v : E → F} {x : E} {c A D K : ℝ}
    (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x)
    (hv : DifferentiableAt ℝ v x) (hc : 0 ≤ c)
    (ha₀ : ‖a x‖ ≤ 1) (hb₀ : ‖b x‖ ≤ 1) (hv₀ : ‖v x‖ ≤ 1)
    (ha₁ : ‖fderiv ℝ a x‖ ≤ A) (hb₁ : ‖fderiv ℝ b x‖ ≤ D)
    (hv₁ : ‖fderiv ℝ v x‖ ≤ K) :
    ‖c • (a x • (b x • v x))‖ +
      ‖fderiv ℝ (fun y => c • (a y • (b y • v y))) x‖ ≤
        c * (1 + A + D + K) := by
  have hA : 0 ≤ A := (norm_nonneg _).trans ha₁
  have hD : 0 ≤ D := (norm_nonneg _).trans hb₁
  have hK : 0 ≤ K := (norm_nonneg _).trans hv₁
  have hbv₀ : ‖b x • v x‖ ≤ 1 := by
    rw [norm_smul]
    nlinarith [norm_nonneg (b x), norm_nonneg (v x)]
  have hbv₁ : ‖fderiv ℝ (fun y => b y • v y) x‖ ≤ D + K := by
    apply (norm_fderiv_smul_le hb hv).trans
    nlinarith [norm_nonneg (b x), norm_nonneg (v x),
      norm_nonneg (fderiv ℝ b x), norm_nonneg (fderiv ℝ v x)]
  have hav₀ : ‖a x • (b x • v x)‖ ≤ 1 := by
    rw [norm_smul]
    nlinarith [norm_nonneg (a x), norm_nonneg (b x • v x)]
  have hav₁ : ‖fderiv ℝ (fun y => a y • (b y • v y)) x‖ ≤ A + D + K := by
    have hh := norm_fderiv_smul_le ha (hb.smul hv)
    change ‖fderiv ℝ (fun y => a y • (b y • v y)) x‖ ≤
      ‖a x‖ * ‖fderiv ℝ (fun y => b y • v y) x‖ +
        ‖fderiv ℝ a x‖ * ‖b x • v x‖ at hh
    apply hh.trans
    calc
      _ ≤ 1 * (D + K) + A * 1 := add_le_add
        (mul_le_mul ha₀ hbv₁ (norm_nonneg _) (by norm_num))
        (mul_le_mul ha₁ hbv₀ (norm_nonneg _) hA)
      _ = A + D + K := by ring
  have hd : DifferentiableAt ℝ (fun y => a y • (b y • v y)) x :=
    ha.fun_smul (hb.fun_smul hv)
  have hcv₀ : ‖c • (a x • (b x • v x))‖ ≤ c := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
    nlinarith
  have hcv₁ : ‖fderiv ℝ (fun y => c • (a y • (b y • v y))) x‖ ≤
      c * (A + D + K) := by
    rw [fderiv_fun_const_smul hd c, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
    exact mul_le_mul_of_nonneg_left hav₁ hc
  nlinarith

theorem norm_fderiv_comp_le
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E → F} {g : F → G} {x : E}
    (hg : DifferentiableAt ℝ g (f x)) (hf : DifferentiableAt ℝ f x) :
    ‖fderiv ℝ (g ∘ f) x‖ ≤ ‖fderiv ℝ g (f x)‖ * ‖fderiv ℝ f x‖ := by
  rw [fderiv_comp x hg hf]
  exact ContinuousLinearMap.opNorm_comp_le _ _

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.LocalPredictionInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340

theorem norm_add_fderiv_predictionSummand_scaled_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α : E → ℝ} {β : ℝ → ℝ} {T : ℕ → E → ℝ} {Φ : ℕ → E → F}
    {A D J K B L : ℝ} {n : ℕ} {x : E}
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hJ : 0 ≤ J) (hK : 0 ≤ K)
    (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hα : DifferentiableAt ℝ α x) (hβ : DifferentiableAt ℝ β (T n x))
    (hT : DifferentiableAt ℝ (T n) x) (hΦ : DifferentiableAt ℝ (Φ n) x)
    (hα₀ : ‖α x‖ ≤ 1) (hβ₀ : ‖β (T n x)‖ ≤ 1) (hΦ₀ : ‖Φ n x‖ ≤ 1)
    (hα₁ : ‖fderiv ℝ α x‖ ≤ A)
    (hβ₁ : ‖fderiv ℝ β (T n x)‖ ≤ D)
    (hT₁ : ‖fderiv ℝ (T n) x‖ ≤ J * B ^ (n + 1))
    (hΦ₁ : ‖fderiv ℝ (Φ n) x‖ ≤ K * (1 + 2 ^ (n + 2))) :
    ‖predictionSummand α β T Φ L n x‖ +
      ‖fderiv ℝ (predictionSummand α β T Φ L n) x‖ ≤
        predictionMajorant ((1 + A + D * J + K) / 10) B L n := by
  have hβT : ‖fderiv ℝ (β ∘ T n) x‖ ≤ (D * J) * B ^ (n + 1) := by
    have h := (norm_fderiv_comp_le hβ hT).trans
      (mul_le_mul hβ₁ hT₁ (norm_nonneg _) hD)
    simpa only [mul_assoc] using h
  have hm := norm_add_fderiv_predictionTerm_le hα (hβ.comp x hT) hΦ
    (c := (L⁻¹) ^ n / 10) (by positivity)
    hα₀ hβ₀ hΦ₀ hα₁ hβT hΦ₁
  change ‖predictionSummand α β T Φ L n x‖ +
    ‖fderiv ℝ (predictionSummand α β T Φ L n) x‖ ≤
      (L⁻¹) ^ n / 10 * (1 + A + (D * J) * B ^ (n + 1) + K * (1 + 2 ^ (n + 2))) at hm
  apply hm.trans
  have hDJ : 0 ≤ D * J := mul_nonneg hD hJ
  have hpB : 0 ≤ B ^ (n + 1) := pow_nonneg hB _
  have hp2 : 0 ≤ (2 : ℝ) ^ (n + 2) := by positivity
  have he : 1 + A + (D * J) * B ^ (n + 1) + K * (1 + 2 ^ (n + 2)) ≤
      (1 + A + D * J + K) * (1 + B ^ (n + 1) + 2 ^ (n + 2)) := by
    nlinarith [mul_nonneg (show 0 ≤ 1 + A + K by linarith) hpB,
      mul_nonneg (show 0 ≤ 1 + A + D * J by linarith) hp2]
  have hfinal := mul_le_mul_of_nonneg_left he (show 0 ≤ (L⁻¹) ^ n / 10 by positivity)
  convert hfinal using 1
  simp only [predictionMajorant]
  ring

theorem contDiffOn_predictionInput
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {s : Set E} {α : E → ℝ} {β : ℝ → ℝ}
    {T : ℕ → E → ℝ} {Φ : ℕ → E → F} {A D J K B L : ℝ}
    (hs : IsOpen s)
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hJ : 0 ≤ J) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hBL : B < L) (hL : 2 < L)
    (hα : ContDiffOn ℝ 1 α s) (hβ : ContDiff ℝ 1 β)
    (hT : ∀ n, ContDiffOn ℝ 1 (T n) s)
    (hΦ : ∀ n, ContDiffOn ℝ 1 (Φ n) s)
    (hα₀ : ∀ x ∈ s, ‖α x‖ ≤ 1)
    (hβ₀ : ∀ n x, x ∈ s → ‖β (T n x)‖ ≤ 1)
    (hΦ₀ : ∀ n x, x ∈ s → ‖Φ n x‖ ≤ 1)
    (hα₁ : ∀ x ∈ s, ‖fderiv ℝ α x‖ ≤ A)
    (hβ₁ : ∀ n x, x ∈ s → ‖fderiv ℝ β (T n x)‖ ≤ D)
    (hT₁ : ∀ n x, x ∈ s → ‖fderiv ℝ (T n) x‖ ≤ J * B ^ (n + 1))
    (hΦ₁ : ∀ n x, x ∈ s → ‖fderiv ℝ (Φ n) x‖ ≤ K * (1 + 2 ^ (n + 2))) :
    ContDiffOn ℝ 1 (fun x => ∑' n, predictionSummand α β T Φ L n x) s := by
  apply contDiffOn_tsum_of_norm_add_fderiv_bound hs
    (u := predictionMajorant ((1 + A + D * J + K) / 10) B L)
  · intro n
    exact (hα.smul ((hβ.comp_contDiffOn (hT n)).smul (hΦ n))).const_smul _
  · exact summable_predictionMajorant hB hBL hL
  · intro n x hx
    exact norm_add_fderiv_predictionSummand_scaled_le hA hD hJ hK hB (by linarith)
      ((hα.differentiableOn_one x hx).differentiableAt (hs.mem_nhds hx))
      (hβ.differentiable_one _)
      (((hT n).differentiableOn_one x hx).differentiableAt (hs.mem_nhds hx))
      (((hΦ n).differentiableOn_one x hx).differentiableAt (hs.mem_nhds hx))
      (hα₀ x hx) (hβ₀ n x hx) (hΦ₀ n x hx)
      (hα₁ x hx) (hβ₁ n x hx) (hT₁ n x hx) (hΦ₁ n x hx)

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.NormalizedPrediction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ContDiff

namespace Problem340.NormalizedPrediction

open AmbientRetraction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {G : ℝ × E → ℝ × E}

theorem contDiffOn_iterate {n : ℕ∞ω} (hG : ContDiff ℝ n G)
    (hsphere : ∀ x : ℝ × E, ‖x.2‖ = 1 → ‖(G x).2‖ = 1) (m : ℕ) :
    ContDiffOn ℝ n ((G ∘ cylinder)^[m]) cylinderDomain := by
  induction m with
  | zero => exact contDiffOn_id
  | succ m hm =>
      rw [Function.iterate_succ']
      exact (contDiffOn_normalizedPredictor G hG).comp hm
        ((mapsTo_normalizedPredictor G hsphere).iterate m)

theorem norm_fderiv_iterate_le_scaled
    (hG : ContDiff ℝ 1 G)
    (hsphere : ∀ x : ℝ × E, ‖x.2‖ = 1 → ‖(G x).2‖ = 1)
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ x : ℝ × E, ‖x.2‖ = 1 → ‖fderiv ℝ G x‖ ≤ B)
    (m : ℕ) (x : ℝ × E) (hx : x ∈ cylinderDomain) :
    ‖fderiv ℝ ((G ∘ cylinder)^[m]) x‖ ≤ 4 * B ^ m := by
  cases m with
  | zero =>
      have hid := ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := ℝ × E)
      simpa only [Function.iterate_zero, fderiv_id, pow_zero, mul_one] using
        hid.trans (by norm_num : (1 : ℝ) ≤ 4)
  | succ m =>
      have hxpos : 0 < ‖x.2‖ := by
        change (1 / 2 : ℝ) < ‖x.2‖ at hx
        linarith
      have heq : ((G ∘ cylinder)^[m + 1]) =ᶠ[nhds x]
          (G^[m + 1] ∘ cylinder) := by
        filter_upwards [isOpen_cylinderDomain.mem_nhds hx] with y hy
        have hypos : 0 < ‖y.2‖ := by
          change (1 / 2 : ℝ) < ‖y.2‖ at hy
          linarith
        exact normalizedPredictor_iterate_succ_eq G hsphere (norm_pos_iff.mp hypos) m
      have hnorm : ‖(cylinder x).2‖ = 1 :=
        mem_sphere_zero_iff_norm.mp (normalize_mem_sphere (norm_pos_iff.mp hxpos))
      have hinv : Set.MapsTo G {y : ℝ × E | ‖y.2‖ = 1}
          {y : ℝ × E | ‖y.2‖ = 1} := hsphere
      obtain ⟨hd, hb⟩ := Prediction.differentiableAt_iterate_and_norm_le_on
        (fun y _ => hG.differentiable one_ne_zero y) hinv hB
        (fun y hy => hbound y hy) (m + 1) (cylinder x) hnorm
      rw [heq.fderiv_eq, fderiv_comp x hd
        ((contDiffAt_cylinder (n := 1) (norm_pos_iff.mp hxpos)).differentiableAt one_ne_zero)]
      calc
        ‖(fderiv ℝ (G^[m + 1]) (cylinder x)).comp (fderiv ℝ cylinder x)‖
            ≤ ‖fderiv ℝ (G^[m + 1]) (cylinder x)‖ * ‖fderiv ℝ cylinder x‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ B ^ (m + 1) * 4 := mul_le_mul hb (norm_fderiv_cylinder_le_four (le_of_lt hx))
          (norm_nonneg (fderiv ℝ (cylinder (E := E)) x)) (pow_nonneg hB _)
        _ = 4 * B ^ (m + 1) := mul_comm _ _

theorem contDiffOn_clock {n : ℕ∞ω} (hG : ContDiff ℝ n G)
    (hsphere : ∀ x : ℝ × E, ‖x.2‖ = 1 → ‖(G x).2‖ = 1) (m : ℕ) :
    ContDiffOn ℝ n (clock G m) cylinderDomain :=
  (contDiffOn_iterate hG hsphere m).fst

theorem norm_fderiv_clock_le_scaled
    (hG : ContDiff ℝ 1 G)
    (hsphere : ∀ x : ℝ × E, ‖x.2‖ = 1 → ‖(G x).2‖ = 1)
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ x : ℝ × E, ‖x.2‖ = 1 → ‖fderiv ℝ G x‖ ≤ B)
    (m : ℕ) (x : ℝ × E) (hx : x ∈ cylinderDomain) :
    ‖fderiv ℝ (clock G m) x‖ ≤ 4 * B ^ m := by
  have hd := ((contDiffOn_iterate hG hsphere m).contDiffAt
    (isOpen_cylinderDomain.mem_nhds hx)).differentiableAt one_ne_zero
  change ‖fderiv ℝ ((ContinuousLinearMap.fst ℝ ℝ E) ∘ (G ∘ cylinder)^[m]) x‖ ≤ _
  rw [fderiv_comp x (ContinuousLinearMap.fst ℝ ℝ E).differentiableAt hd,
    (ContinuousLinearMap.fst ℝ ℝ E).fderiv]
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  calc
    ‖ContinuousLinearMap.fst ℝ ℝ E‖ * ‖fderiv ℝ ((G ∘ cylinder)^[m]) x‖
        ≤ 1 * (4 * B ^ m) := mul_le_mul (ContinuousLinearMap.norm_fst_le ..)
          (norm_fderiv_iterate_le_scaled hG hsphere hB hbound m x hx)
          (norm_nonneg (fderiv ℝ ((G ∘ cylinder)^[m]) x)) (by norm_num)
    _ = 4 * B ^ m := one_mul _

theorem clock_eq_original_on_sphere
    (hsphere : ∀ x : ℝ × E, ‖x.2‖ = 1 → ‖(G x).2‖ = 1)
    {x : ℝ × E} (hx : ‖x.2‖ = 1) (m : ℕ) : clock G m x = (G^[m] x).1 := by
  unfold clock
  rw [normalizedPredictor_iterate_eq G hsphere hx m]

end Problem340.NormalizedPrediction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SphereCutoffTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.SphereCutoffs

@[simp]
theorem clockGate_sphereOfComplex (z : ℂ) :
    clockGate (sphereOfComplex z) = affineClockGate z :=
  clockGate_eq_affineClockGate (sphereOfComplex_val_two z)

@[simp]
theorem clockGate_chartNorthPole : clockGate chartNorthPole = 1 := by
  apply clockGateAmbient_eq_one
  norm_num [chartNorthPole, chartNorthVector]

@[simp]
theorem clockGate_complexSphereHomeomorph (z : OnePoint ℂ) :
    clockGate (complexSphereHomeomorph z) = onePointClockGate z := by
  induction z using OnePoint.rec with
  | infty => simp
  | coe z => simp

end Problem340.SphereCutoffs

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SphereDoublingCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped OnePoint

namespace Problem340

lemma stereoCoordinate_sphereOfComplex (z : ℂ) :
    SphereDoubling.stereoCoordinate (sphereOfComplex z).val = z := by
  unfold SphereDoubling.stereoCoordinate
  simp only [sphereOfComplex_val_zero, sphereOfComplex_val_one, sphereOfComplex_val_two]
  push_cast
  have hd : ((‖z‖ : ℝ) : ℂ) ^ 2 + 1 ≠ 0 := by
    have h : (‖z‖ ^ 2 + 1 : ℝ) ≠ 0 := by positivity
    simpa using Complex.ofReal_ne_zero.mpr h
  have hden : (1 : ℂ) - (((‖z‖ : ℝ) : ℂ) ^ 2 - 1) /
      (((‖z‖ : ℝ) : ℂ) ^ 2 + 1) =
      2 / (((‖z‖ : ℝ) : ℂ) ^ 2 + 1) := by
    field_simp
    ring
  rw [hden]
  field_simp
  have hz := Complex.re_add_im z
  linear_combination hz

lemma stereoCoordinate_eq_sphereToComplex {x : StandardSphere2} (hx : x ≠ chartNorthPole) :
    SphereDoubling.stereoCoordinate x.val = sphereToComplex x := by
  rw [← sphereOfComplex_sphereToComplex hx, stereoCoordinate_sphereOfComplex]
  simp

lemma sphereDoubling_sphereOfComplex (z : ℂ) :
    SphereDoubling.sphereMap (sphereOfComplex z) = sphereOfComplex (z ^ 2) := by
  have hz : sphereOfComplex z ≠ SphereDoubling.north := by
    rw [doubling_north_eq_chartNorthPole]
    exact sphereOfComplex_ne_north z
  have hq : SphereDoubling.sphereMap (sphereOfComplex z) ≠ chartNorthPole := by
    rw [← doubling_north_eq_chartNorthPole]
    exact mt (SphereDoubling.sphereMap_eq_north_iff _).mp hz
  rw [← sphereOfComplex_sphereToComplex hq]
  congr 1
  rw [← stereoCoordinate_eq_sphereToComplex hq]
  rw [SphereDoubling.stereoCoordinate_sphereMap hz, stereoCoordinate_sphereOfComplex]

lemma sphereDoubling_complexSphereHomeomorph (z : OnePoint ℂ) :
    SphereDoubling.sphereMap (complexSphereHomeomorph z) =
      complexSphereHomeomorph (OnePoint.map (fun w : ℂ => w ^ 2) z) := by
  induction z using OnePoint.rec with
  | infty =>
    simp [← doubling_north_eq_chartNorthPole]
  | coe z =>
    simpa using sphereDoubling_sphereOfComplex z

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.PredictionModelBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped OnePoint

namespace Problem340

theorem ambientClockGate_model_eq (z : OnePoint ℂ) :
    SphereCutoffs.clockGateAmbient (complexSphereHomeomorph z).val =
      SphereCutoffs.onePointClockGate z :=
  SphereCutoffs.clockGate_complexSphereHomeomorph z

namespace PredictionModelBridge

theorem semiconj_prediction (D : Construction.SphereData)
    (hgate : D.gate = SphereCutoffs.onePointClockGate) :
    Function.Semiconj modelEmbedding (Construction.prediction D)
      AmbientPrediction.predictor := by
  intro x
  apply Prod.ext
  · simp [modelEmbedding, Construction.prediction, AmbientPrediction.predictor,
      hgate, ambientClockGate_model_eq]
  · simpa [modelEmbedding, Construction.prediction, AmbientPrediction.predictor,
      perturbedSquare, SphereDoubling.sphereMap] using
      congrArg Subtype.val (sphereDoubling_complexSphereHomeomorph x.2).symm

theorem predictedClock_eq (D : Construction.SphereData)
    (hgate : D.gate = SphereCutoffs.onePointClockGate)
    (m : ℕ) (t : ℝ) (z : OnePoint ℂ) :
    Construction.predictedClock D m t z =
      AmbientPrediction.clockPrediction m (modelEmbedding (t, z)) := by
  exact congrArg Prod.fst ((semiconj_prediction D hgate).iterate_right m (t, z))

end PredictionModelBridge

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SphereAngularInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped Topology

namespace Problem340.SphereAngularInput

theorem contDiffAt_phase {n : ℕ∞} {x : SphereAmbient} (hx : horizontal x ≠ 0) :
    ContDiffAt ℝ n phase x := by
  have hn : ContDiffAt ℝ n (fun y => (‖horizontal y‖ : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x
      (contDiff_horizontal.contDiffAt.norm ℂ hx)
  exact (hn.inv (by simpa using hx)).mul contDiff_horizontal.contDiffAt

theorem contDiffAt_angularAmbient_of_horizontal {n : ℕ∞} {x : SphereAmbient}
    (hx : horizontal x ≠ 0) (k : ℕ) : ContDiffAt ℝ n (angularAmbient k) x := by
  exact (Complex.ofRealCLM.contDiff.comp
    SphereCutoffs.contDiff_preparationCutoffAmbient).contDiffAt.mul
      ((contDiffAt_phase hx).pow k)

theorem angularAmbient_eq_zero_of_low {x : SphereAmbient} (hx : x 2 ≤ -4 / 5) (k : ℕ) :
    angularAmbient k x = 0 := by
  simp [angularAmbient, SphereCutoffs.preparationCutoffAmbient_eq_zero_of_low hx]

theorem angularAmbient_eq_zero_of_high {x : SphereAmbient} (hx : 1 / 2 ≤ x 2) (k : ℕ) :
    angularAmbient k x = 0 := by
  simp [angularAmbient, SphereCutoffs.preparationCutoffAmbient_eq_zero_of_high hx]

theorem contDiffAt_angularAmbient_of_low {n : ℕ∞} {x : SphereAmbient}
    (hx : x 2 < -4 / 5) (k : ℕ) : ContDiffAt ℝ n (angularAmbient k) x := by
  apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
  have hh : ContinuousAt (fun y : SphereAmbient => y 2) x :=
    (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous.continuousAt
  filter_upwards [hh.eventually (gt_mem_nhds hx)] with y hy
  exact angularAmbient_eq_zero_of_low hy.le k

theorem contDiffAt_angularAmbient_of_high {n : ℕ∞} {x : SphereAmbient}
    (hx : 1 / 2 < x 2) (k : ℕ) : ContDiffAt ℝ n (angularAmbient k) x := by
  apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
  have hh : ContinuousAt (fun y : SphereAmbient => y 2) x :=
    (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous.continuousAt
  filter_upwards [hh.eventually (lt_mem_nhds hx)] with y hy
  exact angularAmbient_eq_zero_of_high hy.le k

theorem isOpen_regularDomain : IsOpen regularDomain := by
  have hh := (@contDiff_horizontal 0).continuous
  have hz := (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous
  exact (isOpen_ne.preimage hh).union
    ((isOpen_lt hz continuous_const).union (isOpen_lt continuous_const hz))

theorem contDiffOn_angularAmbient {n : ℕ∞} (k : ℕ) :
    ContDiffOn ℝ n (angularAmbient k) regularDomain := by
  apply isOpen_regularDomain.contDiffOn_iff.mpr
  intro x hx
  rcases hx with hx | hx | hx
  · exact contDiffAt_angularAmbient_of_horizontal hx k
  · exact contDiffAt_angularAmbient_of_low hx k
  · exact contDiffAt_angularAmbient_of_high hx k

theorem sphere_mem_regularDomain (x : StandardSphere2) : x.1 ∈ regularDomain := by
  by_cases hh : horizontal x.1 = 0
  · have h0 : x.1 0 = 0 := by simpa [horizontal] using congrArg Complex.re hh
    have h1 : x.1 1 = 0 := by simpa [horizontal] using congrArg Complex.im hh
    have hn : ‖x.1‖ = 1 := by simp
    have hs := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => ℝ) x.1
    have hh2 : (x.1 2) ^ 2 = 1 := by
      simpa [Fin.sum_univ_succ, hn, h0, h1, Real.norm_eq_abs] using hs.symm
    rcases (sq_eq_one_iff).mp hh2 with hp | hm
    · exact Or.inr (Or.inr (by rw [hp]; norm_num))
    · exact Or.inr (Or.inl (by rw [hm]; norm_num))
  · exact Or.inl hh

theorem norm_phase_le_one (x : SphereAmbient) : ‖phase x‖ ≤ 1 := by
  by_cases hx : horizontal x = 0
  · simp [phase, hx]
  · simp [phase, norm_inv, norm_ne_zero_iff.mpr hx]

theorem norm_angularAmbient_le_one (k : ℕ) (x : SphereAmbient) :
    ‖angularAmbient k x‖ ≤ 1 := by
  rw [angularAmbient, norm_mul, norm_pow]
  refine (mul_le_of_le_one_left (by positivity) ?_).trans
    (pow_le_one₀ (norm_nonneg _) (norm_phase_le_one x))
  · simpa [abs_of_nonneg (SphereCutoffs.preparationCutoffAmbient_nonneg x)] using
      SphereCutoffs.preparationCutoffAmbient_le_one x

theorem norm_phase_eq_one {x : SphereAmbient} (hx : horizontal x ≠ 0) : ‖phase x‖ = 1 := by
  simp [phase, norm_inv, norm_ne_zero_iff.mpr hx]

theorem fderiv_angularAmbient_eq_zero_of_low {x : SphereAmbient}
    (hx : x 2 < -4 / 5) (k : ℕ) : fderiv ℝ (angularAmbient k) x = 0 := by
  have hh : ContinuousAt (fun y : SphereAmbient => y 2) x :=
    (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous.continuousAt
  have hz : angularAmbient k =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) := by
    filter_upwards [hh.eventually (gt_mem_nhds hx)] with y hy
    exact angularAmbient_eq_zero_of_low hy.le k
  simpa using hz.fderiv_eq (𝕜 := ℝ)

theorem fderiv_angularAmbient_eq_zero_of_high {x : SphereAmbient}
    (hx : 1 / 2 < x 2) (k : ℕ) : fderiv ℝ (angularAmbient k) x = 0 := by
  have hh : ContinuousAt (fun y : SphereAmbient => y 2) x :=
    (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous.continuousAt
  have hz : angularAmbient k =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) := by
    filter_upwards [hh.eventually (lt_mem_nhds hx)] with y hy
    exact angularAmbient_eq_zero_of_high hy.le k
  simpa using hz.fderiv_eq (𝕜 := ℝ)

theorem norm_fderiv_angularAmbient_le_at {A B : ℝ} {x : SphereAmbient}
    (hx : horizontal x ≠ 0)
    (hA : ‖fderiv ℝ (fun y => (SphereCutoffs.preparationCutoffAmbient y : ℂ)) x‖ ≤ A)
    (hB : ‖fderiv ℝ phase x‖ ≤ B) (k : ℕ) :
    ‖fderiv ℝ (angularAmbient k) x‖ ≤ A + (k : ℝ) * B := by
  have hχ : DifferentiableAt ℝ (fun y => (SphereCutoffs.preparationCutoffAmbient y : ℂ)) x :=
    (Complex.ofRealCLM.contDiff.comp
      (SphereCutoffs.contDiff_preparationCutoffAmbient (n := 1))).differentiable (by norm_num) x
  have hψ : DifferentiableAt ℝ phase x :=
    (contDiffAt_phase (n := 1) hx).differentiableAt (by norm_num)
  have hunit := norm_phase_eq_one hx
  have hχnorm : ‖(SphereCutoffs.preparationCutoffAmbient x : ℂ)‖ ≤ 1 := by
    simpa [abs_of_nonneg (SphereCutoffs.preparationCutoffAmbient_nonneg x)] using
      SphereCutoffs.preparationCutoffAmbient_le_one x
  have hpow : ‖fderiv ℝ (fun y => phase y ^ k) x‖ =
      (k : ℝ) * ‖fderiv ℝ phase x‖ := by
    rw [fderiv_fun_pow k hψ]
    simp [norm_smul, nsmul_eq_mul, norm_pow, hunit]
  unfold angularAmbient
  rw [fderiv_fun_mul hχ (hψ.fun_pow k)]
  calc
    _ ≤ ‖(SphereCutoffs.preparationCutoffAmbient x : ℂ) •
          fderiv ℝ (fun y => phase y ^ k) x‖ +
        ‖phase x ^ k • fderiv ℝ (fun y => (SphereCutoffs.preparationCutoffAmbient y : ℂ)) x‖ :=
      norm_add_le _ _
    _ = ‖(SphereCutoffs.preparationCutoffAmbient x : ℂ)‖ *
        ((k : ℝ) * ‖fderiv ℝ phase x‖) +
        ‖fderiv ℝ (fun y => (SphereCutoffs.preparationCutoffAmbient y : ℂ)) x‖ := by
      simp only [norm_smul, norm_pow, hunit, one_pow, one_mul, hpow]
    _ ≤ 1 * ((k : ℝ) * B) + A := by
      exact add_le_add
        (mul_le_mul hχnorm (mul_le_mul_of_nonneg_left hB (Nat.cast_nonneg k))
          (mul_nonneg (Nat.cast_nonneg k) (norm_nonneg _)) (by norm_num)) hA
    _ = A + (k : ℝ) * B := by ring

theorem exists_uniform_angular_bound_on_compact {K : Set SphereAmbient}
    (hK : IsCompact K) (hU : K ⊆ regularDomain) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (k : ℕ) (x : SphereAmbient), x ∈ K →
      ‖angularAmbient k x‖ + ‖fderiv ℝ (angularAmbient k) x‖ ≤ C * (1 + (k : ℝ)) := by
  let belt : Set SphereAmbient := K ∩ {x | -4 / 5 ≤ x 2 ∧ x 2 ≤ 1 / 2}
  have hz := (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous
  have hbelt : IsCompact belt := hK.inter_right
    ((isClosed_le continuous_const hz).inter (isClosed_le hz continuous_const))
  have hregular : ∀ x ∈ belt, horizontal x ≠ 0 := by
    intro x hx
    rcases hU hx.1 with hh | hlo | hhi
    · exact hh
    · linarith [hx.2.1]
    · linarith [hx.2.2]
  have hχ : ContDiff ℝ 1 (fun y => (SphereCutoffs.preparationCutoffAmbient y : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp SphereCutoffs.contDiff_preparationCutoffAmbient
  obtain ⟨A, hA⟩ := hK.exists_bound_of_continuousOn
    (hχ.continuous_fderiv (by norm_num)).continuousOn
  have hphase : ContinuousOn (fderiv ℝ phase) belt := by
    intro x hx
    exact ((contDiffAt_phase (n := 1) (hregular x hx)).continuousAt_fderiv
      (by norm_num)).continuousWithinAt
  obtain ⟨B, hB⟩ := hbelt.exists_bound_of_continuousOn hphase
  have hA0 : 0 ≤ max 0 A := le_max_left _ _
  have hB0 : 0 ≤ max 0 B := le_max_left _ _
  refine ⟨1 + max 0 A + max 0 B, by linarith, ?_⟩
  intro k x hx
  have hd : ‖fderiv ℝ (angularAmbient k) x‖ ≤ max 0 A + (k : ℝ) * max 0 B := by
    by_cases hxb : x ∈ belt
    · exact norm_fderiv_angularAmbient_le_at (hregular x hxb)
        ((hA x hx).trans (le_max_right _ _)) ((hB x hxb).trans (le_max_right _ _)) k
    · have hnot : ¬ (-4 / 5 ≤ x 2 ∧ x 2 ≤ 1 / 2) := fun h => hxb ⟨hx, h⟩
      rcases not_and_or.mp hnot with hlo | hhi
      · rw [fderiv_angularAmbient_eq_zero_of_low (lt_of_not_ge hlo) k, norm_zero]
        positivity
      · rw [fderiv_angularAmbient_eq_zero_of_high (lt_of_not_ge hhi) k, norm_zero]
        positivity
  have hv := norm_angularAmbient_le_one k x
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  nlinarith [mul_nonneg hA0 hk]

theorem exists_uniform_angular_neighborhood :
    ∃ (U : Set SphereAmbient) (C : ℝ), IsOpen U ∧
      Metric.sphere (0 : SphereAmbient) 1 ⊆ U ∧ 1 ≤ C ∧
      (∀ k : ℕ, ContDiffOn ℝ (⊤ : ℕ∞) (angularAmbient k) U) ∧
      ∀ (k : ℕ) (x : SphereAmbient), x ∈ U →
        ‖angularAmbient k x‖ + ‖fderiv ℝ (angularAmbient k) x‖ ≤ C * (1 + (k : ℝ)) := by
  have hs := isCompact_sphere (0 : SphereAmbient) 1
  have hsub : Metric.sphere (0 : SphereAmbient) 1 ⊆ regularDomain :=
    fun x hx => sphere_mem_regularDomain ⟨x, hx⟩
  obtain ⟨δ, hδ, hδU⟩ := hs.exists_cthickening_subset_open isOpen_regularDomain hsub
  obtain ⟨C, hC, hbound⟩ := exists_uniform_angular_bound_on_compact hs.cthickening hδU
  refine ⟨Metric.thickening δ (Metric.sphere (0 : SphereAmbient) 1), C,
    Metric.isOpen_thickening, Metric.self_subset_thickening hδ _, hC, ?_, ?_⟩
  · intro k
    exact (contDiffOn_angularAmbient (n := ⊤) k).mono
      ((Metric.thickening_subset_cthickening _ _).trans hδU)
  · intro k x hx
    exact hbound k x (Metric.thickening_subset_cthickening _ _ hx)

theorem phase_eq_normalize (x : SphereAmbient) :
    phase x = NormedSpace.normalize (horizontal x) := by
  simp [phase, NormedSpace.normalize, Complex.real_smul]

theorem phase_eq_of_positive_scale {x : SphereAmbient} {z : ℂ} {r : ℝ}
    (hr : 0 < r) (hx : horizontal x = r • z) :
    phase x = NormedSpace.normalize z := by
  rw [phase_eq_normalize, hx, NormedSpace.normalize_smul_of_pos hr]

end Problem340.SphereAngularInput

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.ConcreteInputRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.ConcreteInputRegularity

theorem predictor_preserves_norm (x : Ambient) (hx : ‖x.2‖ = 1) :
    ‖(AmbientPrediction.predictor x).2‖ = 1 := by
  exact mem_sphere_zero_iff_norm.mp
    (SphereDoubling.ambientMap_mem_sphere ⟨x.2, mem_sphere_zero_iff_norm.mpr hx⟩)

theorem exists_contDiffOn_ambientInput_product :
    ∃ (B : ℝ) (W : Set SphereAmbient), 1 ≤ B ∧ IsOpen W ∧
      Metric.sphere (0 : SphereAmbient) 1 ⊆ W ∧
      ∀ L : ℝ, B < L → 2 < L → ∀ i : Fin 3,
        ContDiffOn ℝ 1 (ambientInput L i) (Set.univ ×ˢ W) := by
  obtain ⟨B, hB, hBbound⟩ := AmbientPrediction.exists_derivative_bound
  obtain ⟨U, K, hU, hsU, hK, hangular, hangularBound⟩ :=
    SphereAngularInput.exists_uniform_angular_neighborhood
  obtain ⟨A, hA, hAbound⟩ := exists_preparationCoeff_fderiv_bound
  obtain ⟨D, hD, hDbound⟩ := exists_readoutCoeff_fderiv_bound
  let V : Set Ambient := AmbientRetraction.cylinderDomain ∩ Prod.snd ⁻¹' U
  have hV : IsOpen V := AmbientRetraction.isOpen_cylinderDomain.inter
    (hU.preimage continuous_snd)
  have hVsub : AmbientPrediction.cylinder ⊆ V := by
    intro x hx
    refine ⟨?_, hsU hx.2⟩
    change (1 / 2 : ℝ) < ‖x.2‖
    rw [mem_sphere_zero_iff_norm.mp hx.2]
    norm_num
  have hpred : ContDiff ℝ 1 AmbientPrediction.predictor :=
    AmbientPrediction.contDiff_predictor
  have hnormBound : ∀ x : Ambient, ‖x.2‖ = 1 →
      ‖fderiv ℝ AmbientPrediction.predictor x‖ ≤ B := by
    intro x hx
    exact hBbound x ⟨Set.mem_univ _, mem_sphere_zero_iff_norm.mpr hx⟩
  let W : Set SphereAmbient := {z | (0, z) ∈ V}
  have hW : IsOpen W := hV.preimage (continuous_const.prodMk continuous_id)
  have hsW : Metric.sphere (0 : SphereAmbient) 1 ⊆ W :=
    fun z hz => hVsub ⟨Set.mem_univ _, hz⟩
  have hVW : V = Set.univ ×ˢ W := by
    ext x
    simp [V, W, AmbientRetraction.cylinderDomain]
  refine ⟨B, W, hB, hW, hsW, ?_⟩
  intro L hBL hL i
  rw [← hVW]
  apply contDiffOn_predictionInput hV (A := A) (D := D) (J := 4) (K := K)
    (B := B) (by linarith) (by linarith) (by norm_num) (by linarith)
    (by linarith) hBL hL
  · exact (preparationCoeff_contDiff.comp contDiff_fst).contDiffOn
  · exact readoutCoeff_contDiff i
  · intro n
    exact (NormalizedPrediction.contDiffOn_clock hpred predictor_preserves_norm
      (n + 1)).mono (fun _ hx => hx.1)
  · intro n
    exact ((hangular (2 ^ (n + 2))).of_le (by norm_num)).comp
      contDiffOn_snd (fun _ hx => hx.2)
  · intro x _
    change ‖preparationCoeff x.1‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (preparationCoeff_nonneg x.1)]
    exact preparationCoeff_le_one x.1
  · intro n x _
    rw [Real.norm_eq_abs, abs_of_nonneg (readoutCoeff_nonneg i _)]
    exact readoutCoeff_le_one i _
  · intro n x _
    exact SphereAngularInput.norm_angularAmbient_le_one _ _
  · intro x _
    have hh := norm_fderiv_comp_le
      ((preparationCoeff_contDiff (n := 1)).differentiable_one x.1)
      (differentiableAt_fst (p := x))
    change ‖fderiv ℝ preparation x‖ ≤ A
    apply hh.trans
    calc
      ‖fderiv ℝ preparationCoeff x.1‖ * ‖fderiv ℝ Prod.fst x‖
          ≤ A * 1 := mul_le_mul (hAbound x.1)
            (by rw [fderiv_fst]; exact ContinuousLinearMap.norm_fst_le ℝ ℝ SphereAmbient)
            (norm_nonneg _) (by linarith)
      _ = A := mul_one A
  · intro n x _
    exact hDbound i _
  · intro n x hx
    exact NormalizedPrediction.norm_fderiv_clock_le_scaled hpred predictor_preserves_norm
      (by linarith) hnormBound (n + 1) x hx.1
  · intro n x hx
    have hd : DifferentiableAt ℝ
        (SphereAngularInput.angularAmbient (2 ^ (n + 2))) x.2 :=
      (((hangular (2 ^ (n + 2))).of_le (by norm_num)).contDiffAt
        (hU.mem_nhds hx.2)).differentiableAt one_ne_zero
    have hh := norm_fderiv_comp_le hd (differentiableAt_snd (p := x))
    change ‖fderiv ℝ (angular n) x‖ ≤ K * (1 + 2 ^ (n + 2))
    apply hh.trans
    have hb : ‖fderiv ℝ (SphereAngularInput.angularAmbient (2 ^ (n + 2))) x.2‖ ≤
        K * (1 + (2 : ℝ) ^ (n + 2)) := by
      have := hangularBound (2 ^ (n + 2)) x.2 hx.2
      push_cast at this
      linarith [norm_nonneg (SphereAngularInput.angularAmbient (2 ^ (n + 2)) x.2)]
    calc
      _ ≤ (K * (1 + (2 : ℝ) ^ (n + 2))) * 1 := mul_le_mul hb
        (by rw [fderiv_snd]; exact ContinuousLinearMap.norm_snd_le ℝ ℝ SphereAmbient)
        (norm_nonneg _) (by positivity)
      _ = K * (1 + 2 ^ (n + 2)) := mul_one _

theorem ambientInput_eq_zero_of_preparation_eq_zero
    (L : ℝ) (i : Fin 3) (x : Ambient) (h : preparationCoeff x.1 = 0) :
    ambientInput L i x = 0 := by
  simp [ambientInput, predictionSummand, preparation, h]

theorem ambientInput_eq_zero_of_not_mem (L : ℝ) (i : Fin 3) (x : Ambient)
    (hx : x.1 ∉ Set.Ioo (8 : ℝ) 12) : ambientInput L i x = 0 := by
  apply ambientInput_eq_zero_of_preparation_eq_zero
  by_contra h
  exact hx (preparationCoeff_support ▸ h)

open scoped OnePoint

theorem horizontal_sphereOfComplex (z : ℂ) :
    SphereAngularInput.horizontal (sphereOfComplex z).val =
      (2 / (‖z‖ ^ 2 + 1) : ℝ) • z := by
  calc
    _ = (2 / (‖z‖ ^ 2 + 1) : ℝ) • ((z.re : ℂ) + (z.im : ℂ) * Complex.I) := by
      simp only [SphereAngularInput.horizontal, sphereOfComplex_val_zero,
        sphereOfComplex_val_one, Complex.real_smul]
      push_cast
      ring
    _ = _ := by rw [Complex.re_add_im]

theorem phase_complexSphereHomeomorph (z : OnePoint ℂ) :
    SphereAngularInput.phase (complexSphereHomeomorph z).val = Construction.phase z := by
  induction z using OnePoint.rec with
  | infty =>
      simp [SphereAngularInput.phase, SphereAngularInput.horizontal,
        chartNorthPole, chartNorthVector, Fin.ext_iff]
  | coe z =>
      rw [complexSphereHomeomorph_coe,
        SphereAngularInput.phase_eq_of_positive_scale
          (by positivity : (0 : ℝ) < 2 / (‖z‖ ^ 2 + 1))
          (horizontal_sphereOfComplex z)]
      simp [NormedSpace.normalize, Construction.phase_coe, Complex.real_smul,
        div_eq_mul_inv, mul_comm]

theorem cutoff_complexSphereHomeomorph (z : OnePoint ℂ) :
    SphereCutoffs.preparationCutoffAmbient (complexSphereHomeomorph z).val =
      SphereCutoffs.onePointPreparationCutoff z := by
  induction z using OnePoint.rec with
  | infty =>
      change SphereCutoffs.preparationCutoffAmbient chartNorthPole.val = 0
      apply SphereCutoffs.preparationCutoffAmbient_eq_zero_of_high
      norm_num [chartNorthPole, chartNorthVector, PiLp.single_apply, Fin.ext_iff]
  | coe z =>
      simp [SphereCutoffs.preparationCutoffAmbient,
        SphereCutoffs.affinePreparationCutoff, SphereCutoffs.affineHeight]

theorem angular_modelEmbedding (n : ℕ) (t : ℝ) (z : OnePoint ℂ) :
    angular n (PredictionModelBridge.modelEmbedding (t, z)) =
      (SphereCutoffs.onePointPreparationCutoff z : ℂ) *
        Construction.phase z ^ (2 ^ (n + 2)) := by
  change SphereAngularInput.angularAmbient _ (complexSphereHomeomorph z).val = _
  rw [SphereAngularInput.angularAmbient, phase_complexSphereHomeomorph,
    cutoff_complexSphereHomeomorph]

theorem predictedClock_modelEmbedding (D : Construction.SphereData)
    (hgate : D.gate = SphereCutoffs.onePointClockGate)
    (n : ℕ) (t : ℝ) (z : OnePoint ℂ) :
    predictedClock n (PredictionModelBridge.modelEmbedding (t, z)) =
      Construction.predictedClock D (n + 1) t z := by
  have hx : ‖(PredictionModelBridge.modelEmbedding (t, z)).2‖ = 1 :=
    mem_sphere_zero_iff_norm.mp (complexSphereHomeomorph z).property
  have hn := NormalizedPrediction.clock_eq_original_on_sphere
    (G := AmbientPrediction.predictor) predictor_preserves_norm hx (n + 1)
  exact hn.trans (PredictionModelBridge.predictedClock_eq D hgate (n + 1) t z).symm

theorem summand_modelEmbedding (D : Construction.SphereData)
    (hgate : D.gate = SphereCutoffs.onePointClockGate)
    (hcutoff : D.cutoff = SphereCutoffs.onePointPreparationCutoff)
    (i : Fin 3) (n : ℕ) (t : ℝ) (z : OnePoint ℂ) :
    predictionSummand preparation (readoutCoeff i) predictedClock angular D.L n
        (PredictionModelBridge.modelEmbedding (t, z)) =
      ((preparationCoeff t / 10 : ℝ) : ℂ) * Construction.inputTerm D i n t z := by
  rw [predictionSummand, predictedClock_modelEmbedding D hgate,
    angular_modelEmbedding]
  simp only [preparation, PredictionModelBridge.modelEmbedding, Construction.inputTerm,
    hcutoff, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_pow, Complex.ofReal_inv, Complex.ofReal_ofNat]
  ring

theorem ambientInput_modelEmbedding (D : Construction.SphereData)
    (hgate : D.gate = SphereCutoffs.onePointClockGate)
    (hcutoff : D.cutoff = SphereCutoffs.onePointPreparationCutoff)
    (i : Fin 3) (t : ℝ) (z : OnePoint ℂ) :
    ambientInput D.L i (PredictionModelBridge.modelEmbedding (t, z)) =
      Construction.baseInput D i t z := by
  unfold ambientInput Construction.baseInput
  rw [← tsum_mul_left]
  exact tsum_congr (fun n => summand_modelEmbedding D hgate hcutoff i n t z)

end Problem340.ConcreteInputRegularity

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.ClockProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340

lemma gainProfile_nonzero_mem {L t : ℝ} (h : gainProfile L t ≠ 0) :
    t ∈ Set.Ioo (6 : ℝ) 96 := by
  by_contra ht
  exact h (gainProfile_zero_outside ht)

lemma periodicGain_contDiff (L : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (periodicGain L) := by
  apply (ClockPeriodization.contDiff_periodize (P := 100) (a := 6) (b := 96)
    (by norm_num) ((gainProfile_contDiff L).comp contDiff_fst) ?_).comp
    (contDiff_id.prodMk contDiff_const)
  intro x hx
  exact ⟨(gainProfile_nonzero_mem hx).1.le, (gainProfile_nonzero_mem hx).2.le⟩

lemma periodicGain_periodic (L : ℝ) : Function.Periodic (periodicGain L) 100 := by
  intro t
  exact ClockPeriodization.periodize_add_period 100
    (fun x : ℝ × ℝ => gainProfile L x.1) t 0

lemma periodicGain_eq {L t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 100) :
    periodicGain L t = gainProfile L t := by
  apply ClockPeriodization.periodize_eq_on_fundamental (by norm_num) ?_ ht (0 : ℝ)
  intro x hx
  obtain ⟨hx0, hx1⟩ := gainProfile_nonzero_mem hx
  constructor <;> linarith

section CircleLift

lemma gainProfile_liftIco_coe_eq_periodicGain (L t : ℝ) :
    AddCircle.liftIco (100 : ℝ) 0 (gainProfile L) (t : AddCircle (100 : ℝ)) =
      periodicGain L t := by
  let r := AddCircle.equivIco (100 : ℝ) 0 (t : AddCircle (100 : ℝ))
  have hr : (r : ℝ) ∈ Set.Icc (0 : ℝ) 100 := by
    simpa only [zero_add] using Set.Ico_subset_Icc_self r.property
  have hrep : ((r : ℝ) : AddCircle (100 : ℝ)) = (t : AddCircle (100 : ℝ)) :=
    AddCircle.coe_equivIco
  have hp := periodicGain_periodic L
  calc
    AddCircle.liftIco (100 : ℝ) 0 (gainProfile L) (t : AddCircle (100 : ℝ)) =
        gainProfile L r := rfl
    _ = periodicGain L r := (periodicGain_eq hr).symm
    _ = hp.lift ((r : ℝ) : AddCircle (100 : ℝ)) := (hp.lift_coe _).symm
    _ = hp.lift (t : AddCircle (100 : ℝ)) := congrArg hp.lift hrep
    _ = periodicGain L t := hp.lift_coe t

end CircleLift

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.GainLocalExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff

namespace Problem340

attribute [local instance] OAI.Problem340.instFactLtRealOfNat_solutions_1
lemma standardGain_param (L t : ℝ) :
    standardGain L (clockHomeomorph (t : AddCircle (100 : ℝ))) = periodicGain L t := by
  simp only [standardGain, clockHomeomorph.symm_apply_apply,
    gainProfile_liftIco_coe_eq_periodicGain]

theorem standardGain_hasLocalC1Extension (L : ℝ) :
    HasLocalC1Extension (fun x : StandardClock => x.1) (standardGain L) := by
  apply hasLocalC1Extension_of_clock_lift
  simpa only [standardGain_param] using (periodicGain_contDiff L).of_le
    (show (1 : ℕ∞ω) ≤ (⊤ : ℕ∞) by simp)

theorem standardGain_hasLocalC1Extension_manifold (L : ℝ) (q : ℕ) :
    HasLocalC1Extension (standardEmbedding q)
      (fun x : CounterexampleManifold q => standardGain L x.1) :=
  (standardGain_hasLocalC1Extension L).clock_coordinate

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SphereCompactSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Filter Metric
open scoped Topology ContDiff RealInnerProductSpace

namespace Problem340
namespace SphereCompactSupport

variable {E W : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {v : E} (hv : ‖v‖ = 1)

omit [NormedSpace ℝ W] in
theorem extension_of_ne (F : (ℝ ∙ v)ᗮ → W) {x : sphere (0 : E) 1}
    (hx : (x : E) ≠ v) : extension F x = F (stereoToFun v x) := by
  simp [extension, hx]

include hv in

theorem exists_local_ambient_extension
    {F : (ℝ ∙ v)ᗮ → W} (hF : ContDiff ℝ ∞ F) (hFc : HasCompactSupport F)
    (x : sphere (0 : E) 1) :
    ∃ U : Set E, IsOpen U ∧ (x : E) ∈ U ∧ ∃ A : E → W,
      ContDiffOn ℝ ∞ A U ∧
      ∀ y : sphere (0 : E) 1, (y : E) ∈ U → extension F y = A y := by
  by_cases hx : (x : E) = v
  · let K : Set E := (fun w : (ℝ ∙ v)ᗮ => (stereoInvFun hv w : E)) '' tsupport F
    have hK : IsCompact K := hFc.image
      (continuous_subtype_val.comp (continuous_stereoInvFun hv))
    have hvK : v ∉ K := by
      rintro ⟨w, hw, heq⟩
      exact stereoInvFun_ne_north_pole hv w (Subtype.ext heq)
    refine ⟨Kᶜ, hK.isClosed.isOpen_compl, ?_, fun _ => 0, contDiffOn_const, ?_⟩
    · simpa [hx] using hvK
    · intro y hy
      by_cases hyv : (y : E) = v
      · simp [extension, hyv]
      · rw [extension_of_ne F hyv]
        by_contra hne
        apply hy
        refine ⟨stereoToFun v y, subset_closure hne, ?_⟩
        exact congrArg Subtype.val (stereo_left_inv hv hyv)
  · let U : Set E := {y | innerSL ℝ v y ≠ (1 : ℝ)}
    have hU : IsOpen U := isOpen_ne_fun (innerSL ℝ v).continuous continuous_const
    have hxU : (x : E) ∈ U := by
      intro h
      exact hx ((inner_eq_one_iff_of_norm_eq_one hv (norm_eq_of_mem_sphere x)).mp h).symm
    refine ⟨U, hU, hxU, F ∘ stereoToFun v, ?_, ?_⟩
    · exact hF.comp_contDiffOn contDiffOn_stereoToFun
    · intro y hy
      apply extension_of_ne
      intro hyv
      apply hy
      simp [hyv, hv]

end SphereCompactSupport
end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.StandardSaturation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Filter Metric
open scoped Topology ContDiff

namespace Problem340

theorem saturationOnEquator_contDiff (R : ℝ) (hR : 1 ≤ R) :
    ContDiff ℝ ∞ (saturationOnEquator R hR) :=
  (saturation_contDiff R hR).comp
    (chartEquatorEquiv.symm.contDiff.const_smul (1 / 2 : ℝ))

theorem saturationOnEquator_hasCompactSupport (R : ℝ) (hR : 1 ≤ R) :
    HasCompactSupport (saturationOnEquator R hR) := by
  convert (saturation_hasCompactSupport R hR).comp_homeomorph scaledChartEquator.symm using 1
  funext w
  simp [saturationOnEquator, scaledChartEquator, div_eq_mul_inv]

@[simp] theorem standardSphereSaturation_affine (R : ℝ) (hR : 1 ≤ R) (z : ℂ) :
    standardSphereSaturation R hR (sphereOfComplex z) = saturation R hR z := by
  unfold standardSphereSaturation
  rw [SphereCompactSupport.extension_of_ne]
  · change saturation R hR (sphereToComplex (sphereOfComplex z)) = _
    rw [sphereToComplex_sphereOfComplex]
  · intro h
    exact sphereOfComplex_ne_north z (Subtype.ext h)

theorem standardSphereSaturation_eq_transport (R : ℝ) (hR : 1 ≤ R) (x : StandardSphere2) :
    standardSphereSaturation R hR x = sphereSaturation R hR (complexSphereHomeomorph.symm x) := by
  obtain ⟨z, rfl⟩ := complexSphereHomeomorph.surjective x
  induction z using OnePoint.rec with
  | infty => simp
  | coe z => simp

theorem standardSphereSaturation_local_ambient (R : ℝ) (hR : 1 ≤ R)
    (x : StandardSphere2) :
    ∃ U : Set SphereAmbient, IsOpen U ∧ (x : SphereAmbient) ∈ U ∧
      ∃ A : SphereAmbient → ℂ, ContDiffOn ℝ ∞ A U ∧
        ∀ y : StandardSphere2, (y : SphereAmbient) ∈ U →
          standardSphereSaturation R hR y = A y :=
  SphereCompactSupport.exists_local_ambient_extension norm_chartNorthVector
    (saturationOnEquator_contDiff R hR) (saturationOnEquator_hasCompactSupport R hR) x

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.StandardRegisterUpdate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set
open scoped ContDiff

namespace Problem340

@[simp] theorem standardRegisterUpdate_affine (R : ℝ) (hR : 1 ≤ R)
    (a : ℝ) (c z : ℂ) :
    standardRegisterUpdate R hR a c (sphereOfComplex z) =
      sphereOfComplex (a • saturation R hR z + c) := by
  simp [standardRegisterUpdate]

theorem standardRegisterUpdate_eq_transport (R : ℝ) (hR : 1 ≤ R)
    (a : ℝ) (c : ℂ) (x : StandardSphere2) :
    standardRegisterUpdate R hR a c x =
      complexSphereHomeomorph
        ((a • sphereSaturation R hR (complexSphereHomeomorph.symm x) + c : ℂ) : OnePoint ℂ) := by
  simp only [complexSphereHomeomorph_coe, standardRegisterUpdate,
    standardSphereSaturation_eq_transport]

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.MapRegisterRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.Construction

theorem registerOutputInStandardCoordinates_eq_raw (L : ℝ) (hL : 2 < L)
    (i : Fin 3) (x : CounterexampleManifold 3) :
    registerOutputInStandardCoordinates L hL i x =
      complexSphereHomeomorph
        ((concreteMap L hL
          (clockHomeomorph.symm x.1, complexSphereHomeomorph.symm (x.2 0),
            fun j : Fin 3 => complexSphereHomeomorph.symm (x.2 j.succ))).2.2 i) := by
  rw [registerOutputInStandardCoordinates, standardRegisterUpdate_eq_transport]
  simp only [concreteMap, rawMap, registerInputInStandardCoordinates,
    periodicGain, concreteData, standardGain, Complex.real_smul]

theorem concreteSaturation_hasLocalC1Extension (L : ℝ) (hL : 2 < L) :
    HasLocalC1Extension (fun x : StandardSphere2 => x.1)
      (standardSphereSaturation (3 * L) (by linarith)) := by
  intro x
  obtain ⟨U, hU, hx, A, hA, hcomm⟩ :=
    standardSphereSaturation_local_ambient (3 * L) (by linarith) x
  exact ⟨U, hU, hx, A, hA.of_le (by norm_num), hcomm⟩

theorem registerOutputInStandardCoordinates_hasLocalC1Extension
    (L : ℝ) (hL : 2 < L) (i : Fin 3)
    (hinput : HasLocalC1Extension (standardEmbedding 3)
      (registerInputInStandardCoordinates L hL i)) :
    HasLocalC1Extension (standardEmbedding 3)
      (fun x => (registerOutputInStandardCoordinates L hL i x : SphereAmbient)) := by
  have hgain := standardGain_hasLocalC1Extension_manifold L 3
  have hsat := (concreteSaturation_hasLocalC1Extension L hL).sphere_coordinate i.succ
  have hmul := (hgain.prodMk hsat).comp_contDiff
    (show ContDiff ℝ 1 (fun p : ℝ × ℂ => p.1 • p.2) from
      contDiff_fst.smul contDiff_snd)
  have hadd := (hmul.prodMk hinput).comp_contDiff
    (show ContDiff ℝ 1 (fun p : ℂ × ℂ => p.1 + p.2) from
      contDiff_fst.add contDiff_snd)
  simpa only [Function.comp_def, registerOutputInStandardCoordinates,
    standardRegisterUpdate] using hadd.comp_contDiff contDiff_sphereOfComplex_val

end Problem340.Construction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.MapInputRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.Construction

open ConcreteInputRegularity

theorem ambientInput_eq_baseInput_standard (L : ℝ) (hL : 2 < L)
    (i : Fin 3) (t : ℝ) (z : StandardSphere2) :
    ambientInput L i (t, z.val) =
      baseInput (concreteData L hL) i t (complexSphereHomeomorph.symm z) := by
  have h := ambientInput_modelEmbedding (concreteData L hL) rfl rfl i t
    (complexSphereHomeomorph.symm z)
  simpa only [PredictionModelBridge.modelEmbedding, Homeomorph.apply_symm_apply,
    concreteData] using h

theorem liftIco_ambientInput_eq_registerInput (L : ℝ) (hL : 2 < L)
    (i : Fin 3) (x : CounterexampleManifold 3) :
    AddCircle.liftIco (100 : ℝ) 0
      (fun t => ambientInput L i (t, (x.2 0).val)) (clockHomeomorph.symm x.1) =
      registerInputInStandardCoordinates L hL i x := by
  change AddCircle.liftIco (100 : ℝ) 0 _ _ =
    AddCircle.liftIco (100 : ℝ) 0
      (fun t => baseInput (concreteData L hL) i t (complexSphereHomeomorph.symm (x.2 0))) _
  apply congrArg (fun f : ℝ → ℂ =>
    AddCircle.liftIco (100 : ℝ) 0 f (clockHomeomorph.symm x.1))
  funext t
  exact ambientInput_eq_baseInput_standard L hL i t (x.2 0)

theorem exists_registerInput_hasLocalC1Extension :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (L : ℝ) (hL : 2 < L), B < L → ∀ i : Fin 3,
      HasLocalC1Extension (standardEmbedding 3)
        (registerInputInStandardCoordinates L hL i) := by
  obtain ⟨B, W, hB, hW, hsW, hreg⟩ := exists_contDiffOn_ambientInput_product
  refine ⟨B, hB, ?_⟩
  intro L hL hBL i
  have hs : ∀ x, ambientInput L i x ≠ 0 → x.1 ∈ Set.Ioo (0 : ℝ) 100 := by
    intro x hx
    have hh : x.1 ∈ Set.Ioo (8 : ℝ) 12 := by
      by_contra hn
      exact hx (ambientInput_eq_zero_of_not_mem L i x hn)
    constructor <;> linarith [hh.1, hh.2]
  have hp := ClockQuotient.hasLocalC1Extension_liftIco_of_strip_support_on hW
    (hreg L hBL hL i) hs
  let k : CounterexampleManifold 3 → StandardClock × W :=
    fun x => (x.1, ⟨(x.2 0).val, hsW (x.2 0).property⟩)
  let K : CounterexampleAmbient 3 → ClockAmbient × SphereAmbient :=
    fun x => (x.1, x.2 0)
  have hK : ContDiff ℝ 1 K :=
    contDiff_fst.prodMk ((contDiff_apply ℝ SphereAmbient (0 : Fin 4)).comp contDiff_snd)
  have hpull := hp.precomp_ambient (eY := standardEmbedding 3) k K hK (fun _ => rfl)
  have heq : (fun x : StandardClock × W =>
      AddCircle.liftIco (100 : ℝ) 0 (fun t => ambientInput L i (t, x.2.val))
        (clockHomeomorph.symm x.1)) ∘ k = registerInputInStandardCoordinates L hL i := by
    funext x
    exact liftIco_ambientInput_eq_registerInput L hL i x
  rwa [heq] at hpull

end Problem340.Construction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.ReadoutLocalExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ContDiff

namespace Problem340

attribute [local instance] OAI.Problem340.instFactLtRealOfNat_solutions
private lemma reader_nonzero_mem (i : Fin 3) {t : ℝ} (h : readoutCoeff i t ≠ 0) :
    t ∈ Set.Ioo (74 : ℝ) 80 := by
  apply readoutInterval_subset i
  rw [← readoutCoeff_support]
  exact h

lemma periodicReadoutReal_contDiff (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (periodicReadoutReal i) := by
  apply (ClockPeriodization.contDiff_periodize (P := 100) (a := 74) (b := 80)
    (by norm_num) ((readoutCoeff_contDiff i).comp contDiff_fst) ?_).comp
    (contDiff_id.prodMk contDiff_const)
  intro x hx
  exact ⟨(reader_nonzero_mem i hx).1.le, (reader_nonzero_mem i hx).2.le⟩

lemma periodicReadoutReal_periodic (i : Fin 3) :
    Function.Periodic (periodicReadoutReal i) 100 := by
  intro t
  exact ClockPeriodization.periodize_add_period 100
    (fun x : ℝ × ℝ => readoutCoeff i x.1) t 0

lemma periodicReadoutReal_eq (i : Fin 3) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 100) :
    periodicReadoutReal i t = readoutCoeff i t := by
  apply ClockPeriodization.periodize_eq_on_fundamental (by norm_num) ?_ ht (0 : ℝ)
  intro x hx
  obtain ⟨hx0, hx1⟩ := reader_nonzero_mem i hx
  constructor <;> linarith

lemma readoutCoeff_liftIco_coe_eq_periodic (i : Fin 3) (t : ℝ) :
    AddCircle.liftIco (100 : ℝ) 0 (readoutCoeff i) (t : AddCircle (100 : ℝ)) =
      periodicReadoutReal i t := by
  let r := AddCircle.equivIco (100 : ℝ) 0 (t : AddCircle (100 : ℝ))
  have hr : (r : ℝ) ∈ Set.Icc (0 : ℝ) 100 := by
    simpa only [zero_add] using Set.Ico_subset_Icc_self r.property
  have hrep : ((r : ℝ) : AddCircle (100 : ℝ)) = (t : AddCircle (100 : ℝ)) :=
    AddCircle.coe_equivIco
  have hp := periodicReadoutReal_periodic i
  calc
    AddCircle.liftIco (100 : ℝ) 0 (readoutCoeff i) (t : AddCircle (100 : ℝ)) =
        readoutCoeff i r := rfl
    _ = periodicReadoutReal i r := (periodicReadoutReal_eq i hr).symm
    _ = hp.lift ((r : ℝ) : AddCircle (100 : ℝ)) := (hp.lift_coe _).symm
    _ = hp.lift (t : AddCircle (100 : ℝ)) := congrArg hp.lift hrep
    _ = periodicReadoutReal i t := hp.lift_coe t

lemma standardReader_param (i : Fin 3) (t : ℝ) :
    standardReader i (clockHomeomorph (t : AddCircle (100 : ℝ))) =
      periodicReadoutReal i t := by
  simp only [standardReader, clockHomeomorph.symm_apply_apply,
    readoutCoeff_liftIco_coe_eq_periodic]

theorem standardReader_hasLocalC1Extension (i : Fin 3) :
    HasLocalC1Extension (fun x : StandardClock => x.1) (standardReader i) := by
  apply hasLocalC1Extension_of_clock_lift
  simpa only [standardReader_param] using (periodicReadoutReal_contDiff i).of_le
    (show (1 : ℕ∞ω) ≤ (⊤ : ℕ∞) by simp)

theorem standardReader_hasLocalC1Extension_manifold (i : Fin 3) (q : ℕ) :
    HasLocalC1Extension (standardEmbedding q)
      (fun x : CounterexampleManifold q => standardReader i x.1) :=
  (standardReader_hasLocalC1Extension i).clock_coordinate

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SphereTranslation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340
namespace SphereTranslation

lemma isOpen_domain : IsOpen domain := by
  exact isOpen_ne_fun (contDiff_denom 0).continuous continuous_const

lemma contDiffOn_ambient (n : WithTop ℕ∞) :
    ContDiffOn ℝ n (fun p : ℂ × SphereAmbient => ambient p.1 p.2) domain := by
  have hd := (contDiff_denom n).contDiffOn (s := domain)
  have hn : ∀ p ∈ domain, denom p.1 p.2 ≠ 0 := fun p hp => hp
  apply contDiffOn_euclidean.mpr
  intro i
  fin_cases i
  · change ContDiffOn ℝ n
      (fun p : ℂ × SphereAmbient => 2 * (p.2 0 + p.1.re * (1 - p.2 2)) /
        denom p.1 p.2) domain
    apply ContDiffOn.div _ hd hn
    fun_prop
  · change ContDiffOn ℝ n
      (fun p : ℂ × SphereAmbient => 2 * (p.2 1 + p.1.im * (1 - p.2 2)) /
        denom p.1 p.2) domain
    apply ContDiffOn.div _ hd hn
    fun_prop
  · change ContDiffOn ℝ n
      (fun p : ℂ × SphereAmbient => 1 - 2 * (1 - p.2 2) / denom p.1 p.2) domain
    apply contDiffOn_const.sub
    apply ContDiffOn.div _ hd hn
    fun_prop

@[continuity, fun_prop] theorem continuous_translate :
    Continuous (fun p : ℂ × StandardSphere2 => translate p.1 p.2) := by
  apply Continuous.subtype_mk
  rw [continuous_iff_continuousAt]
  intro p
  have hp : (p.1, p.2.1) ∈ domain := ne_of_gt (denom_pos p.1 p.2)
  have hc := ((contDiffOn_ambient 0).contDiffAt (isOpen_domain.mem_nhds hp)).continuousAt
  change ContinuousAt
    ((fun q : ℂ × SphereAmbient => ambient q.1 q.2) ∘
      (fun q : ℂ × StandardSphere2 => (q.1, q.2.1))) p
  exact hc.comp (f := fun q : ℂ × StandardSphere2 => (q.1, q.2.1)) (continuous_fst.prodMk
    (continuous_subtype_val.comp continuous_snd)).continuousAt

lemma contDiffAt_ambient (n : WithTop ℕ∞) (c : ℂ) (x : StandardSphere2) :
    ContDiffAt ℝ n (fun p : ℂ × SphereAmbient => ambient p.1 p.2) (c, x.1) :=
  (contDiffOn_ambient n).contDiffAt
    (isOpen_domain.mem_nhds (ne_of_gt (denom_pos c x)))

lemma ambient_not_north (c : ℂ) (x : StandardSphere2) (hx : x.1 2 ≠ 1) :
    ambient c x.1 2 ≠ 1 := by
  have hd : denom c x.1 ≠ 0 := ne_of_gt (denom_pos c x)
  have ht : 1 - x.1 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  change 1 - 2 * (1 - x.1 2) / denom c x.1 ≠ 1
  intro h
  have hz : 2 * (1 - x.1 2) / denom c x.1 = 0 := by linarith
  exact (div_ne_zero (mul_ne_zero (by norm_num) ht) hd) hz

lemma chart_ambient (c : ℂ) (x : StandardSphere2) (hx : x.1 2 ≠ 1) :
    chart (ambient c x.1) = chart x.1 + c := by
  have hd : denom c x.1 ≠ 0 := ne_of_gt (denom_pos c x)
  have ht : 1 - x.1 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  apply Complex.ext
  · change (2 * (x.1 0 + c.re * (1 - x.1 2)) / denom c x.1) /
      (1 - (1 - 2 * (1 - x.1 2) / denom c x.1)) = x.1 0 / (1 - x.1 2) + c.re
    rw [sub_sub_cancel]
    field_simp [hd, ht]
  · change (2 * (x.1 1 + c.im * (1 - x.1 2)) / denom c x.1) /
      (1 - (1 - 2 * (1 - x.1 2) / denom c x.1)) = x.1 1 / (1 - x.1 2) + c.im
    rw [sub_sub_cancel]
    field_simp [hd, ht]

end SphereTranslation
end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SphereMainUpdate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.SphereMainUpdate

@[continuity, fun_prop] theorem continuous_update :
    Continuous (fun p : ℂ × StandardSphere2 => update p.1 p.2) :=
  SphereTranslation.continuous_translate.comp
    (continuous_fst.prodMk (SphereDoubling.continuous_sphereMap.comp continuous_snd))

theorem contDiffAt_ambient (n : WithTop ℕ∞) (c : ℂ) (x : StandardSphere2) :
    ContDiffAt ℝ n (fun p : ℂ × SphereAmbient => ambient p.1 p.2) (c, x.1) := by
  have hi : ContDiff ℝ n (fun p : ℂ × SphereAmbient =>
      (p.1, SphereDoubling.ambientMap p.2)) :=
    contDiff_fst.prodMk ((SphereDoubling.contDiff_ambientMap n).comp contDiff_snd)
  change ContDiffAt ℝ n
    ((fun q : ℂ × SphereAmbient => SphereTranslation.ambient q.1 q.2) ∘
      (fun p : ℂ × SphereAmbient => (p.1, SphereDoubling.ambientMap p.2))) (c, x.1)
  exact (SphereTranslation.contDiffAt_ambient n c (SphereDoubling.sphereMap x)).comp
    (f := fun p : ℂ × SphereAmbient => (p.1, SphereDoubling.ambientMap p.2))
    (c, x.1) hi.contDiffAt

theorem chart_eq_stereoCoordinate (x : SphereAmbient) :
    SphereTranslation.chart x = SphereDoubling.stereoCoordinate x := by
  unfold SphereTranslation.chart SphereDoubling.stereoCoordinate
  rw [show (1 : ℂ) - (x 2 : ℂ) = ((1 - x 2 : ℝ) : ℂ) by push_cast; rfl]
  rw [Complex.div_ofReal]
  simp

theorem chart_update (c : ℂ) (x : StandardSphere2) (hx : x ≠ SphereDoubling.north) :
    SphereTranslation.chart (update c x).1 = SphereTranslation.chart x.1 ^ 2 + c := by
  rw [update, SphereTranslation.translate]
  rw [SphereTranslation.chart_ambient c (SphereDoubling.sphereMap x)
    (SphereDoubling.ambientMap_third_ne_one (mt (SphereDoubling.eq_north_iff x).mpr hx))]
  rw [chart_eq_stereoCoordinate, SphereDoubling.stereoCoordinate_sphereMap hx,
    chart_eq_stereoCoordinate]

theorem update_ne_north (c : ℂ) (x : StandardSphere2) (hx : x ≠ SphereDoubling.north) :
    update c x ≠ SphereDoubling.north := by
  intro h
  have hn := (SphereDoubling.eq_north_iff (update c x)).mp h
  exact SphereTranslation.ambient_not_north c (SphereDoubling.sphereMap x)
    (SphereDoubling.ambientMap_third_ne_one (mt (SphereDoubling.eq_north_iff x).mpr hx)) hn

@[simp] theorem update_eq_north_iff (c : ℂ) (x : StandardSphere2) :
    update c x = SphereDoubling.north ↔ x = SphereDoubling.north := by
  constructor
  · intro h
    by_contra hx
    exact update_ne_north c x hx h
  · rintro rfl
    exact update_north c

end Problem340.SphereMainUpdate

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SphereChartLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter Topology
open scoped OnePoint

namespace Problem340.SphereChartLimits

theorem north_eq : chartNorthPole = SphereDoubling.north := by
  apply Subtype.ext
  ext i
  fin_cases i <;> simp [chartNorthPole, chartNorthVector, SphereDoubling.north]

theorem chart_sphereOfComplex (z : ℂ) :
    SphereTranslation.chart (sphereOfComplex z).1 = z := by
  have hd : ‖z‖ ^ 2 + 1 ≠ 0 := by positivity
  have hden : 1 - (‖z‖ ^ 2 - 1) / (‖z‖ ^ 2 + 1) = 2 / (‖z‖ ^ 2 + 1) := by
    field_simp
    ring
  apply Complex.ext
  · change (sphereOfComplex z).1 0 / (1 - (sphereOfComplex z).1 2) = z.re
    rw [sphereOfComplex_val_zero, sphereOfComplex_val_two, hden]
    field_simp
  · change (sphereOfComplex z).1 1 / (1 - (sphereOfComplex z).1 2) = z.im
    rw [sphereOfComplex_val_one, sphereOfComplex_val_two, hden]
    field_simp

theorem sphereToComplex_eq_chart {x : StandardSphere2} (hx : x ≠ chartNorthPole) :
    sphereToComplex x = SphereTranslation.chart x.1 := by
  calc
    sphereToComplex x = SphereTranslation.chart (sphereOfComplex (sphereToComplex x)).1 :=
      (chart_sphereOfComplex _).symm
    _ = SphereTranslation.chart x.1 := by rw [sphereOfComplex_sphereToComplex hx]

end Problem340.SphereChartLimits

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SphereMainUpdateTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped OnePoint

namespace Problem340.SphereMainUpdate

@[simp] theorem update_sphereOfComplex (c z : ℂ) :
    update c (sphereOfComplex z) = sphereOfComplex (z ^ 2 + c) := by
  have hz : sphereOfComplex z ≠ SphereDoubling.north := by
    rw [← SphereChartLimits.north_eq]
    exact sphereOfComplex_ne_north z
  have hout : update c (sphereOfComplex z) ≠ chartNorthPole := by
    rw [SphereChartLimits.north_eq]
    exact update_ne_north c _ hz
  calc
    update c (sphereOfComplex z) =
        sphereOfComplex (sphereToComplex (update c (sphereOfComplex z))) :=
      (sphereOfComplex_sphereToComplex hout).symm
    _ = sphereOfComplex (SphereTranslation.chart (update c (sphereOfComplex z)).1) := by
      rw [SphereChartLimits.sphereToComplex_eq_chart hout]
    _ = sphereOfComplex (z ^ 2 + c) := by
      rw [chart_update c _ hz, SphereChartLimits.chart_sphereOfComplex]

theorem update_complexSphereHomeomorph (c : ℂ) (z : OnePoint ℂ) :
    update c (complexSphereHomeomorph z) =
      complexSphereHomeomorph (perturbedSquare c z) := by
  induction z using OnePoint.rec with
  | infty => simp [SphereChartLimits.north_eq]
  | coe z => simp

end Problem340.SphereMainUpdate

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.MapMainRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped Topology ContDiff

namespace Problem340.Construction

local instance instFactLtRealOfNat_solutions_3_ree851b_1 : Fact ((0 : ℝ) < 100) := ⟨by norm_num⟩
theorem periodicReadout_hasLocalC1Extension (i : Fin 3) :
    HasLocalC1Extension modelEmbedding (fun x : RawManifold => periodicReadout i x.1) := by
  have h := (standardReader_hasLocalC1Extension_manifold i 3).precomp_ambient
    (eY := modelEmbedding) modelHomeomorph id contDiff_id (fun _ => rfl)
  convert h using 1
  funext x
  change periodicReadout i x.1 = standardReader i (ClockModel.clockHomeomorph x.1)
  change periodicReadout i x.1 = standardReader i (clockHomeomorph x.1)
  simp only [standardReader, Homeomorph.symm_apply_apply, periodicReadout]

theorem concrete_saturation_hasLocalC1Extension (L : ℝ) (hL : 2 < L) (i : Fin 3) :
    HasLocalC1Extension modelEmbedding
      (fun x : RawManifold => (concreteData L hL).saturation (x.2.2 i)) := by
  have hs : HasLocalC1Extension (fun x : StandardSphere2 => x.1)
      (standardSphereSaturation (3 * L) (by linarith)) := by
    intro x
    obtain ⟨U, hU, hxU, A, hA, heq⟩ :=
      standardSphereSaturation_local_ambient (3 * L) (by linarith) x
    exact ⟨U, hU, hxU, A, hA.of_le (by simp), heq⟩
  have h := (hs.sphere_coordinate (q := 3) i.succ).precomp_ambient
    (eY := modelEmbedding) modelHomeomorph id contDiff_id (fun _ => rfl)
  convert h using 1
  funext x
  rw [Function.comp_apply, modelHomeomorph_register,
    standardSphereSaturation_eq_transport, Homeomorph.symm_apply_apply]
  rfl

theorem concrete_readout_hasLocalC1Extension (L : ℝ) (hL : 2 < L) :
    HasLocalC1Extension modelEmbedding
      (fun x : RawManifold => readout (concreteData L hL) x.1 x.2.2) := by
  have hb := HasLocalC1Extension.pi (fun i => periodicReadout_hasLocalC1Extension i)
  have hs := HasLocalC1Extension.pi (fun i => concrete_saturation_hasLocalC1Extension L hL i)
  have hp : ContDiff ℝ 1 (fun p : (Fin 3 → ℝ) × (Fin 3 → ℂ) =>
      (20 : ℂ) * ∑ i : Fin 3, (p.1 i : ℂ) * p.2 i) := by
    apply contDiff_const.mul
    apply ContDiff.sum
    intro i hi
    exact (Complex.ofRealCLM.contDiff.comp
      ((contDiff_apply ℝ ℝ i).comp contDiff_fst)).mul
      ((contDiff_apply ℝ ℂ i).comp contDiff_snd)
  exact (hb.prodMk hs).comp_contDiff hp

theorem mainUpdate_hasLocalC1Extension :
    HasLocalC1Extension (fun p : ℂ × StandardSphere2 => (p.1, p.2.1))
      (fun p => (SphereMainUpdate.update p.1 p.2).1) := by
  intro p
  obtain ⟨U, hU, hA⟩ :=
    (SphereMainUpdate.contDiffAt_ambient 1 p.1 p.2).contDiffOn le_rfl (by simp)
  obtain ⟨V, hVU, hV, hpV⟩ := mem_nhds_iff.mp hU
  exact ⟨V, hV, hpV, fun q => SphereMainUpdate.ambient q.1 q.2,
    hA.mono hVU, fun _ _ => rfl⟩

theorem concrete_main_hasLocalC1Extension (L : ℝ) (hL : 2 < L) :
    HasLocalC1Extension modelEmbedding
      (fun x : RawManifold => (complexSphereHomeomorph ((concreteMap L hL x).2.1)).1) := by
  have hm : HasLocalC1Extension modelEmbedding
      (fun x : RawManifold => (complexSphereHomeomorph x.2.1).1) :=
    .of_contDiffOn isOpen_univ (fun _ => Set.mem_univ _)
      (fun p : CounterexampleAmbient 3 => p.2 0)
      (((contDiff_apply ℝ SphereAmbient (0 : Fin 4)).comp contDiff_snd).contDiffOn)
      (fun _ => rfl)
  have h := mainUpdate_hasLocalC1Extension.comp
    (f := fun x : RawManifold =>
      (readout (concreteData L hL) x.1 x.2.2, complexSphereHomeomorph x.2.1))
    ((concrete_readout_hasLocalC1Extension L hL).prodMk hm)
  convert h using 1
  funext x
  exact congrArg Subtype.val
    (SphereMainUpdate.update_complexSphereHomeomorph
      (readout (concreteData L hL) x.1 x.2.2) x.2.1).symm

theorem realizedMap_main_hasLocalC1Extension (L : ℝ) (hL : 2 < L) :
    HasLocalC1Extension (standardEmbedding 3)
      (fun x : CounterexampleManifold 3 => ((realizedMap L hL x).2 0).1) := by
  have h := (concrete_main_hasLocalC1Extension L hL).precomp_ambient
    (eY := standardEmbedding 3) modelHomeomorph.symm id contDiff_id
    (fun y => by simp [modelEmbedding])
  convert h using 1
  funext x
  rfl

end Problem340.Construction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.RealizedRegisterRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.Construction

theorem realizedMap_register_eq_standardOutput
    (L : ℝ) (hL : 2 < L) (i : Fin 3) (x : CounterexampleManifold 3) :
    (realizedMap L hL x).2 i.succ = registerOutputInStandardCoordinates L hL i x := by
  rw [registerOutputInStandardCoordinates_eq_raw]
  rfl

theorem realizedMap_register_hasLocalC1Extension
    (L : ℝ) (hL : 2 < L) (i : Fin 3)
    (hinput : HasLocalC1Extension (standardEmbedding 3)
      (registerInputInStandardCoordinates L hL i)) :
    HasLocalC1Extension (standardEmbedding 3)
      (fun x => ((realizedMap L hL x).2 i.succ).1) := by
  simpa only [realizedMap_register_eq_standardOutput] using
    registerOutputInStandardCoordinates_hasLocalC1Extension L hL i hinput

end Problem340.Construction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.MapC1Complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.Construction

theorem exists_threshold_isC1SelfMap_realizedMap :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (L : ℝ) (hL : 2 < L), B < L →
      IsC1SelfMap 3 (realizedMap L hL) := by
  obtain ⟨B, hB, hinput⟩ := exists_registerInput_hasLocalC1Extension
  refine ⟨B, hB, ?_⟩
  intro L hL hBL
  apply isC1SelfMap_realizedMap_of_sphere_components L hL
    (realizedMap_main_hasLocalC1Extension L hL)
  intro i
  exact realizedMap_register_hasLocalC1Extension L hL i (hinput L hL hBL i)

theorem exists_isC1SelfMap_realizedMap :
    ∃ (L : ℝ) (hL : 2 < L), IsC1SelfMap 3 (realizedMap L hL) := by
  obtain ⟨B, hB, hreg⟩ := exists_threshold_isC1SelfMap_realizedMap
  have hL : 2 < B + 3 := by linarith
  exact ⟨B + 3, hL, hreg (B + 3) hL (by linarith)⟩

end Problem340.Construction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.HomotopySpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340

variable {X : Type} [TopologicalSpace X]
  {f g : X → X} (hf : Continuous f) (hg : Continuous g)

theorem homologyRadiusSet_eq_of_homotopy
    (H : ContinuousMap.Homotopy (continuousMapOf f hf) (continuousMapOf g hg)) :
    {r : ℝ | ∃ n : ℕ, ∃ a b : ℝ, ∃ u v : RealSingularHomology n X,
      (u ≠ 0 ∨ v ≠ 0) ∧
      realHomologyMap n f hf u = a • u - b • v ∧
      realHomologyMap n f hf v = b • u + a • v ∧
      r = Real.sqrt (a ^ 2 + b ^ 2)} =
    {r : ℝ | ∃ n : ℕ, ∃ a b : ℝ, ∃ u v : RealSingularHomology n X,
      (u ≠ 0 ∨ v ≠ 0) ∧
      realHomologyMap n g hg u = a • u - b • v ∧
      realHomologyMap n g hg v = b • u + a • v ∧
      r = Real.sqrt (a ^ 2 + b ^ 2)} := by
  ext r
  simp only [realHomologyMap_eq_of_homotopy _ hf hg H]

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SkewProductHomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340

theorem continuous_rawSphereSection (q : ℕ) : Continuous (rawSphereSection q) := by
  exact continuous_const.prodMk (continuous_id.prodMk continuous_const)

theorem continuous_rawSphereProjection (q : ℕ) :
    Continuous (@rawSphereProjection q) := continuous_fst.comp continuous_snd

theorem realHomologyMap_rawUpdate_eq_normalForm (n q : ℕ)
    {h : RawState q → ℝ} {C : RawState q → ℂ} {R : RawState q → Fin q → ℂ}
    (hh : Continuous h) (hC : Continuous C) (hR : Continuous R) :
    realHomologyMap n (rawUpdate h C R) (continuous_rawUpdate hh hC hR) =
      realHomologyMap n rawNormalForm continuous_rawNormalForm :=
  (realHomologyMap_eq_of_homotopy n continuous_rawNormalForm
    (continuous_rawUpdate hh hC hR) (rawUpdateHomotopy hh hC hR)).symm

theorem rawUpdate_eigenvector_of_sphere (n q : ℕ)
    {h : RawState q → ℝ} {C : RawState q → ℂ} {R : RawState q → Fin q → ℂ}
    (hh : Continuous h) (hC : Continuous C) (hR : Continuous R)
    (c : ℝ) (v : RealSingularHomology n (OnePoint ℂ)) (hv : v ≠ 0)
    (heig : realHomologyMap n rawSphereSquare continuous_rawSphereSquare v = c • v) :
    ∃ w : RealSingularHomology n (RawState q), w ≠ 0 ∧
      realHomologyMap n (rawUpdate h C R) (continuous_rawUpdate hh hC hR) w = c • w := by
  let s := rawSphereSection q
  have hs : Continuous s := continuous_rawSphereSection q
  have hinj := realHomologyMap_injective_of_retraction n s rawSphereProjection hs
    (continuous_rawSphereProjection q) (rawSphereProjection_section q)
  refine ⟨realHomologyMap n s hs v, ?_, ?_⟩
  · intro hz
    apply hv
    apply hinj
    simpa using hz
  · rw [realHomologyMap_rawUpdate_eq_normalForm n q hh hC hR]
    have H := realHomologyMap_comp n s rawNormalForm hs continuous_rawNormalForm
    change realHomologyMap n (s ∘ rawSphereSquare) (hs.comp continuous_rawSphereSquare) =
      (realHomologyMap n rawNormalForm continuous_rawNormalForm).comp
        (realHomologyMap n s hs) at H
    rw [realHomologyMap_comp n rawSphereSquare s continuous_rawSphereSquare hs] at H
    have Hv := congrArg (fun k => k v) H.symm
    simpa [heig] using Hv

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.MapHomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.Construction

theorem rawMap_eigenvector_of_sphere (n : ℕ) (D : SphereData)
    (hh : Continuous (rawClockFunction D)) (hC : Continuous (rawPerturbation D))
    (hR : Continuous (rawRegisterFunction D))
    (c : ℝ) (v : RealSingularHomology n Sphere) (hv : v ≠ 0)
    (heig : realHomologyMap n rawSphereSquare continuous_rawSphereSquare v = c • v) :
    ∃ w : RealSingularHomology n RawManifold, w ≠ 0 ∧
      realHomologyMap n (rawMap D) (continuous_rawMap_of_rawCoefficients D hh hC hR) w = c • w :=
  rawUpdate_eigenvector_of_sphere n 3 hh hC hR c v hv heig

theorem concreteMap_eigenvector_of_sphere (n : ℕ) (L : ℝ) (hL : 2 < L)
    (c : ℝ) (v : RealSingularHomology n Sphere) (hv : v ≠ 0)
    (heig : realHomologyMap n rawSphereSquare continuous_rawSphereSquare v = c • v) :
    ∃ w : RealSingularHomology n RawManifold, w ≠ 0 ∧
      realHomologyMap n (concreteMap L hL) (concreteMap_continuous_for_homotopy L hL) w = c • w := by
  obtain ⟨hh, hC, hR⟩ := continuous_concrete_rawCoefficients L hL
  exact rawMap_eigenvector_of_sphere n (concreteData L hL) hh hC hR c v hv heig

end Problem340.Construction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.MapRealizedHomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.Construction

theorem realizedMap_eigenvector_of_sphere (n : ℕ) (L : ℝ) (hL : 2 < L)
    (c : ℝ) (v : RealSingularHomology n Sphere) (hv : v ≠ 0)
    (heig : realHomologyMap n rawSphereSquare continuous_rawSphereSquare v = c • v) :
    ∃ w : RealSingularHomology n (CounterexampleManifold 3), w ≠ 0 ∧
      realHomologyMap n (realizedMap L hL) (continuous_realizedMap_actual L hL) w = c • w := by
  obtain ⟨w, hw, he⟩ := concreteMap_eigenvector_of_sphere n L hL c v hv heig
  exact realizedMap_eigenvector L hL (concreteMap_continuous_for_homotopy L hL)
    n c w hw he

theorem homologyEigenvalueRadii_concreteMap_eq_normalForm (L : ℝ) (hL : 2 < L) :
    homologyEigenvalueRadii (concreteMap L hL) (concreteMap_continuous_for_homotopy L hL) =
      homologyEigenvalueRadii (@rawNormalForm 3) continuous_rawNormalForm :=
  (homologyRadiusSet_eq_of_homotopy continuous_rawNormalForm
    (concreteMap_continuous_for_homotopy L hL) (concreteMapHomotopy L hL)).symm

theorem log_two_le_realizedMap_radius_of_sphere (L : ℝ) (hL : 2 < L)
    (v : RealSingularHomology 2 Sphere) (hv : v ≠ 0)
    (heig : realHomologyMap 2 rawSphereSquare continuous_rawSphereSquare v = (2 : ℝ) • v)
    (hbounded : BddAbove
      (homologyEigenvalueRadii (@rawNormalForm 3) continuous_rawNormalForm)) :
    Real.log (2 : ℝ) ≤ Real.log (totalRealHomologySpectralRadius
      (realizedMap L hL) (continuous_realizedMap_actual L hL)) := by
  obtain ⟨w, hw, he⟩ := concreteMap_eigenvector_of_sphere 2 L hL 2 v hv heig
  have hb : BddAbove (homologyEigenvalueRadii (concreteMap L hL)
      (concreteMap_continuous_for_homotopy L hL)) := by
    rw [homologyEigenvalueRadii_concreteMap_eq_normalForm]
    exact hbounded
  rw [totalRealHomologySpectralRadius_realizedMap]
  exact log_two_le_log_totalRealHomologySpectralRadius
    (concreteMap_continuous_for_homotopy L hL) hb hw he

theorem exists_counterexample_of_concrete_obligations (L : ℝ) (hL : 2 < L)
    (hC1 : IsC1SelfMap 3 (realizedMap L hL))
    (hentropy : Dynamics.coverEntropy (realizedMap L hL) Set.univ = (0 : EReal))
    (hsphere : ∃ v : RealSingularHomology 2 Sphere, v ≠ 0 ∧
      realHomologyMap 2 rawSphereSquare continuous_rawSphereSquare v = (2 : ℝ) • v)
    (hbounded : BddAbove
      (homologyEigenvalueRadii (@rawNormalForm 3) continuous_rawNormalForm)) :
    ∃ q : ℕ, 0 < q ∧ ∃ f : CounterexampleManifold q → CounterexampleManifold q,
      ∃ hf : IsC1SelfMap q f,
        Dynamics.coverEntropy f (Set.univ : Set (CounterexampleManifold q)) = (0 : EReal) ∧
        (∃ v : RealSingularHomology 2 (CounterexampleManifold q),
          v ≠ 0 ∧ realHomologyMap 2 f hf.1 v = (2 : ℝ) • v) ∧
        0 < Real.log (2 : ℝ) ∧
        Real.log (2 : ℝ) ≤ Real.log (totalRealHomologySpectralRadius f hf.1) ∧
        ¬ Function.Bijective f ∧ 5 ≤ 2 * q + 3 := by
  obtain ⟨v, hv, he⟩ := hsphere
  refine ⟨3, by norm_num, realizedMap L hL, hC1, hentropy,
    realizedMap_eigenvector_of_sphere 2 L hL 2 v hv he,
    Real.log_pos (by norm_num), ?_, realizedMap_not_bijective L hL, by norm_num⟩
  exact log_two_le_realizedMap_radius_of_sphere L hL v hv he hbounded

end Problem340.Construction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.MapFinalReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.Construction

open PolynomialSpectrum

theorem homologyEigenvalueRadii_eq_iUnion {X : Type} [TopologicalSpace X]
    (f : X → X) (hf : Continuous f) :
    homologyEigenvalueRadii f hf = ⋃ n, pairRadii (realHomologyMap n f hf) := by
  simp only [homologyEigenvalueRadii, pairRadii, Set.iUnion_ofPred]

theorem bddAbove_normalForm_of_rawBase
    (hB : BddAbove (homologyEigenvalueRadii rawBaseSquare continuous_rawBaseSquare)) :
    BddAbove (homologyEigenvalueRadii (@rawNormalForm 3) continuous_rawNormalForm) := by
  rw [homologyEigenvalueRadii_eq_iUnion] at hB ⊢
  apply bddAbove_homology_pairRadii_of_homotopy_factor
    (@rawNormalForm 3) rawFactorInclusion rawBaseProjection
    continuous_rawNormalForm continuous_rawFactorInclusion continuous_rawBaseProjection
    (ContinuousMap.Homotopy.refl _)
  exact hB

theorem exists_counterexample_of_sphere_and_base_homology
    (hsphere : ∃ v : RealSingularHomology 2 Sphere, v ≠ 0 ∧
      realHomologyMap 2 rawSphereSquare continuous_rawSphereSquare v = (2 : ℝ) • v)
    (hbase : BddAbove
      (homologyEigenvalueRadii rawBaseSquare continuous_rawBaseSquare)) :
    ∃ q : ℕ, 0 < q ∧ ∃ f : CounterexampleManifold q → CounterexampleManifold q,
      ∃ hf : IsC1SelfMap q f,
        Dynamics.coverEntropy f (Set.univ : Set (CounterexampleManifold q)) = (0 : EReal) ∧
        (∃ v : RealSingularHomology 2 (CounterexampleManifold q),
          v ≠ 0 ∧ realHomologyMap 2 f hf.1 v = (2 : ℝ) • v) ∧
        0 < Real.log (2 : ℝ) ∧
        Real.log (2 : ℝ) ≤ Real.log (totalRealHomologySpectralRadius f hf.1) ∧
        ¬ Function.Bijective f ∧ 5 ≤ 2 * q + 3 := by
  obtain ⟨L, hL, hC1⟩ := exists_isC1SelfMap_realizedMap
  exact exists_counterexample_of_concrete_obligations L hL hC1
    (coverEntropy_realizedMap_eq_zero L hL) hsphere
    (bddAbove_normalForm_of_rawBase hbase)

end Problem340.Construction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SubdivisionQuasiIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory

namespace Problem340.SubdivisionComparison

variable {R : Type*} [Ring R]

theorem exists_cycle_representative (S : ShortComplex (ModuleCat R))
    (v : S.homology) :
    ∃ z : S.X₂, ∃ hz : S.g.hom z = 0, moduleHomologyClass S z hz = v := by
  obtain ⟨z, hz⟩ := (LinearMap.range S.moduleCatToCycles).mkQ_surjective
    (S.moduleCatHomologyIso.toLinearEquiv v)
  refine ⟨z.1, z.2, ?_⟩
  apply S.moduleCatHomologyIso.toLinearEquiv.injective
  unfold moduleHomologyClass
  erw [LinearEquiv.apply_symm_apply]
  change (LinearMap.range S.moduleCatToCycles).mkQ z = _
  exact hz

theorem reflect_cycle {S T : ShortComplex (ModuleCat R)} (φ : S ⟶ T)
    (hφ : Function.Injective φ.τ₃.hom) (z : S.X₂)
    (hz : T.g.hom (φ.τ₂.hom z) = 0) : S.g.hom z = 0 := by
  apply hφ
  have h := congrArg (fun k : S.X₂ ⟶ T.X₃ => k.hom z) φ.comm₂₃
  change T.g.hom (φ.τ₂.hom z) = φ.τ₃.hom (S.g.hom z) at h
  simpa only [map_zero] using h.symm.trans hz

theorem class_map_eq_class {S : ShortComplex (ModuleCat R)} (s : S ⟶ S)
    (hs : ShortComplex.homologyMap s = 𝟙 S.homology)
    (z : S.X₂) (hz : S.g.hom z = 0) :
    moduleHomologyClass S (s.τ₂.hom z) (map_cycle s z hz) =
      moduleHomologyClass S z hz := by
  rw [← moduleHomologyClass_map s z hz (map_cycle s z hz), hs]
  rfl

theorem homologyMap_bijective_of_eventual_range
    {S T : ShortComplex (ModuleCat R)} (φ : S ⟶ T)
    (hinj₂ : Function.Injective φ.τ₂.hom)
    (hinj₃ : Function.Injective φ.τ₃.hom)
    (s : ℕ → (T ⟶ T)) (t : ℕ → (S ⟶ S))
    (hcomm : ∀ k, φ ≫ s k = t k ≫ φ)
    (hs : ∀ k, ShortComplex.homologyMap (s k) = 𝟙 T.homology)
    (ht : ∀ k, ShortComplex.homologyMap (t k) = 𝟙 S.homology)
    (hsmall₁ : ∀ y : T.X₁, ∃ k, ∃ x : S.X₁,
      (s k).τ₁.hom y = φ.τ₁.hom x)
    (hsmall₂ : ∀ y : T.X₂, ∃ k, ∃ x : S.X₂,
      (s k).τ₂.hom y = φ.τ₂.hom x) :
    Function.Bijective (ShortComplex.homologyMap φ).hom := by
  constructor
  · apply (injective_iff_map_eq_zero _).mpr
    intro v hv
    obtain ⟨z, hz, rfl⟩ := exists_cycle_representative S v
    rw [moduleHomologyClass_map φ z hz (map_cycle φ z hz)] at hv
    obtain ⟨y, hy⟩ := (moduleHomologyClass_eq_zero_iff T
      (φ.τ₂.hom z) (map_cycle φ z hz)).mp hv
    obtain ⟨k, x, hx⟩ := hsmall₁ y
    have hb : S.f.hom x = (t k).τ₂.hom z := by
      apply hinj₂
      have hφ := congrArg (fun f : S.X₁ ⟶ T.X₂ => f.hom x) φ.comm₁₂
      have hs' := congrArg (fun f : T.X₁ ⟶ T.X₂ => f.hom y) (s k).comm₁₂
      have hc := congrArg (fun f : S ⟶ T => f.τ₂.hom z) (hcomm k)
      change T.f.hom (φ.τ₁.hom x) = φ.τ₂.hom (S.f.hom x) at hφ
      change T.f.hom ((s k).τ₁.hom y) = (s k).τ₂.hom (T.f.hom y) at hs'
      change (s k).τ₂.hom (φ.τ₂.hom z) = φ.τ₂.hom ((t k).τ₂.hom z) at hc
      calc
        φ.τ₂.hom (S.f.hom x) = T.f.hom (φ.τ₁.hom x) := hφ.symm
        _ = T.f.hom ((s k).τ₁.hom y) := congrArg T.f.hom hx.symm
        _ = (s k).τ₂.hom (T.f.hom y) := hs'
        _ = (s k).τ₂.hom (φ.τ₂.hom z) := congrArg (s k).τ₂.hom hy
        _ = φ.τ₂.hom ((t k).τ₂.hom z) := hc
    have hzero := (moduleHomologyClass_eq_zero_iff S
      ((t k).τ₂.hom z) (map_cycle (t k) z hz)).mpr ⟨x, hb⟩
    rw [class_map_eq_class (t k) (ht k) z hz] at hzero
    exact hzero
  · intro v
    obtain ⟨z, hz, rfl⟩ := exists_cycle_representative T v
    obtain ⟨k, x, hx⟩ := hsmall₂ z
    have hφx : T.g.hom (φ.τ₂.hom x) = 0 := by
      rw [← hx]
      exact map_cycle (s k) z hz
    have hxc : S.g.hom x = 0 := reflect_cycle φ hinj₃ x hφx
    refine ⟨moduleHomologyClass S x hxc, ?_⟩
    rw [moduleHomologyClass_map φ x hxc hφx]
    have hclass := class_map_eq_class (s k) (hs k) z hz
    simpa only [hx] using hclass

section Complexes

variable {ι : Type*} {c : ComplexShape ι}
  {C D : HomologicalComplex (ModuleCat R) c}

theorem quasiIso_of_eventual_range
    (φ : C ⟶ D) (hinj : ∀ n, Function.Injective (φ.f n).hom)
    (s : ℕ → (D ⟶ D)) (t : ℕ → (C ⟶ C))
    (hcomm : ∀ k, φ ≫ s k = t k ≫ φ)
    (hs : ∀ k n, HomologicalComplex.homologyMap (s k) n = 𝟙 (D.homology n))
    (ht : ∀ k n, HomologicalComplex.homologyMap (t k) n = 𝟙 (C.homology n))
    (hsmall : ∀ n (y : D.X n), ∃ k, ∃ x : C.X n,
      ((s k).f n).hom y = (φ.f n).hom x) : QuasiIso φ := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap, ConcreteCategory.isIso_iff_bijective]
  let F := HomologicalComplex.shortComplexFunctor (ModuleCat R) c n
  apply homologyMap_bijective_of_eventual_range (F.map φ)
    (hinj n) (hinj (c.next n)) (fun k => F.map (s k)) (fun k => F.map (t k))
  · intro k
    simpa only [Functor.map_comp] using congrArg F.map (hcomm k)
  · exact fun k => hs k n
  · exact fun k => ht k n
  · exact hsmall (c.prev n)
  · exact hsmall n

theorem intertwines_pow (φ : C ⟶ D) (s : End D) (t : End C)
    (hcomm : φ ≫ s = t ≫ φ) (k : ℕ) :
    φ ≫ (s ^ k).asHom = (t ^ k).asHom ≫ φ := by
  induction k with
  | zero => simp
  | succ k hk =>
    simp only [pow_succ, End.mul_def, End.asHom]
    rw [← Category.assoc, hcomm, Category.assoc, hk, Category.assoc]

theorem homologyMap_pow_eq_id (s : End C) (hs : Homotopy s (𝟙 C))
    (k : ℕ) (n : ι) :
    HomologicalComplex.homologyMap (s ^ k).asHom n = 𝟙 (C.homology n) := by
  have hs' := (hs.homologyMap_eq n).trans (HomologicalComplex.homologyMap_id C n)
  induction k with
  | zero => simpa only [pow_zero, End.one_def] using HomologicalComplex.homologyMap_id C n
  | succ k hk =>
    simp only [pow_succ, End.mul_def, End.asHom,
      HomologicalComplex.homologyMap_comp, hs', hk, Category.id_comp]

theorem quasiIso_of_eventual_iterate_range
    (φ : C ⟶ D) (hinj : ∀ n, Function.Injective (φ.f n).hom)
    (s : End D) (t : End C) (hcomm : φ ≫ s = t ≫ φ)
    (hs : Homotopy s (𝟙 D)) (ht : Homotopy t (𝟙 C))
    (hsmall : ∀ n (y : D.X n), ∃ k, ∃ x : C.X n,
      ((s ^ k).asHom.f n).hom y = (φ.f n).hom x) : QuasiIso φ := by
  exact quasiIso_of_eventual_range φ hinj
    (fun k => (s ^ k).asHom) (fun k => (t ^ k).asHom)
    (intertwines_pow φ s t hcomm)
    (homologyMap_pow_eq_id s hs) (homologyMap_pow_eq_id t ht) hsmall

end Complexes

end Problem340.SubdivisionComparison

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SingularSmallComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory

namespace Problem340.SingularSmallChains

variable {X : Type} [TopologicalSpace X] {ι : Type*} (U : ι → Set X)

theorem inclusion_quasiIso_of_natural_subdivision
    (S : singularFunctor ⟶ singularFunctor)
    (H : ∀ Y : TopCat, Homotopy (S.app Y) (𝟙 (singularFunctor.obj Y)))
    (hH : HomotopyNatural (T := 𝟙 singularFunctor) H)
    (hsmall : ∀ n (z : (realSingularChainComplex X).X n), ∃ k : ℕ,
      (((End.of (S.app (TopCat.of X))) ^ k).asHom.f n).hom z ∈
        LinearMap.range ((inclusion U).f n).hom) : QuasiIso (inclusion U) := by
  apply SubdivisionComparison.quasiIso_of_eventual_iterate_range
    (inclusion U) (inclusion_f_injective U)
    (End.of (S.app (TopCat.of X))) (End.of (restrictChainMap U S))
    (restrictChainMap_inclusion U S).symm (H (TopCat.of X))
  · simpa only [restrictChainMap_id] using restrictHomotopy U (S := S) (T := 𝟙 singularFunctor) H hH
  · intro n z
    obtain ⟨k, x, hx⟩ := hsmall n z
    exact ⟨k, x, hx.symm⟩

theorem inclusion_quasiIso_of_natural_subdivision_zero
    (S : singularFunctor ⟶ singularFunctor)
    (hzero : ∀ Y : TopCat, (S.app Y).f 0 = 𝟙 ((singularFunctor.obj Y).X 0))
    (hsmall : ∀ n (z : (realSingularChainComplex X).X n), ∃ k : ℕ,
      (((End.of (S.app (TopCat.of X))) ^ k).asHom.f n).hom z ∈
        LinearMap.range ((inclusion U).f n).hom) : QuasiIso (inclusion U) := by
  apply inclusion_quasiIso_of_natural_subdivision U S
    (SingularAcyclicModels.homotopyApp S (𝟙 _) hzero) _ hsmall
  intro i j Y Z f
  exact SingularAcyclicModels.homotopyApp_naturality S (𝟙 _) hzero f i j

end Problem340.SingularSmallChains

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SimplexSubdivisionMesh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric

namespace Problem340.SimplexSubdivision

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma faceCenter_eq (v : ι → E) (s : Finset ι) :
    faceCenter v s = (s.card : ℝ)⁻¹ • ∑ i ∈ s, v i := by
  simp [faceCenter, Finset.centerMass]

lemma card_smul_faceCenter (v : ι → E) {s : Finset ι} (hs : s.Nonempty) :
    (s.card : ℝ) • faceCenter v s = ∑ i ∈ s, v i := by
  rw [faceCenter_eq, smul_smul, mul_inv_cancel₀, one_smul]
  exact_mod_cast hs.card_ne_zero

lemma sum_sub_faceCenter (v : ι → E) {s : Finset ι} (hs : s.Nonempty) :
    ∑ i ∈ s, (v i - faceCenter v s) = 0 := by
  rw [Finset.sum_sub_distrib, Finset.sum_const,
    ← Nat.cast_smul_eq_nsmul ℝ, card_smul_faceCenter v hs, sub_self]

lemma faceCenter_mem_convexHull (v : ι → E) {s : Finset ι} (hs : s.Nonempty) :
    faceCenter v s ∈ convexHull ℝ (v '' (s : Set ι)) := by
  apply s.centerMass_mem_convexHull (fun _ _ => zero_le_one)
  · simpa using (show (0 : ℝ) < s.card by exact_mod_cast hs.card_pos)
  · intro i hi
    exact ⟨i, hi, rfl⟩

lemma dist_faceCenter_le (v : ι → E) {s : Finset ι} (hs : s.Nonempty)
    (x : E) (D : ℝ) (h : ∀ i ∈ s, dist (v i) x ≤ D) :
    dist (faceCenter v s) x ≤ D := by
  apply (convex_closedBall x D).centerMass_mem (fun _ _ => zero_le_one)
  · simpa using (show (0 : ℝ) < s.card by exact_mod_cast hs.card_pos)
  · exact h

lemma card_smul_faceCenter_sub [DecidableEq ι] (v : ι → E)
    {s t : Finset ι} (hs : s.Nonempty) (hst : s ⊆ t) :
    (t.card : ℝ) • (faceCenter v t - faceCenter v s) =
      ∑ i ∈ t \ s, (v i - faceCenter v s) := by
  have ht : t.Nonempty := hs.mono hst
  calc
    (t.card : ℝ) • (faceCenter v t - faceCenter v s) =
        ∑ i ∈ t, (v i - faceCenter v s) := by
      rw [smul_sub, card_smul_faceCenter v ht, Finset.sum_sub_distrib,
        Finset.sum_const, Nat.cast_smul_eq_nsmul]
    _ = ∑ i ∈ t \ s, (v i - faceCenter v s) := by
      rw [← Finset.sum_sdiff hst, sum_sub_faceCenter v hs, add_zero]

lemma dist_faceCenter_nested_le [DecidableEq ι] (v : ι → E)
    {s t : Finset ι} (hs : s.Nonempty) (hst : s ⊆ t) (D : ℝ)
    (hD : ∀ i ∈ t, ∀ j ∈ t, dist (v i) (v j) ≤ D) :
    dist (faceCenter v s) (faceCenter v t) ≤
      ((t.card - s.card : ℕ) : ℝ) / (t.card : ℝ) * D := by
  have ht : t.Nonempty := hs.mono hst
  have htpos : (0 : ℝ) < t.card := by exact_mod_cast ht.card_pos
  have hbound : (t.card : ℝ) * dist (faceCenter v t) (faceCenter v s) ≤
      ((t \ s).card : ℝ) * D := by
    calc
      (t.card : ℝ) * dist (faceCenter v t) (faceCenter v s) =
          ‖(t.card : ℝ) • (faceCenter v t - faceCenter v s)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg htpos.le, dist_eq_norm]
      _ = ‖∑ i ∈ t \ s, (v i - faceCenter v s)‖ :=
        congrArg norm (card_smul_faceCenter_sub v hs hst)
      _ ≤ ∑ i ∈ t \ s, ‖v i - faceCenter v s‖ := norm_sum_le _ _
      _ ≤ ∑ _i ∈ t \ s, D := by
        apply Finset.sum_le_sum
        intro i hi
        rw [← dist_eq_norm, dist_comm]
        exact dist_faceCenter_le v hs (v i) D
          (fun j hj => hD j (hst hj) i (Finset.mem_sdiff.mp hi).1)
      _ = ((t \ s).card : ℝ) * D := by simp
  calc
    dist (faceCenter v s) (faceCenter v t) =
        dist (faceCenter v t) (faceCenter v s) := dist_comm _ _
    _ ≤ ((t \ s).card : ℝ) * D / (t.card : ℝ) :=
      (le_div_iff₀ htpos).2 (by simpa only [mul_comm] using hbound)
    _ = ((t.card - s.card : ℕ) : ℝ) / (t.card : ℝ) * D := by
      rw [Finset.card_sdiff_of_subset hst]
      ring

lemma dist_faceCenter_nested_le_mesh [DecidableEq ι] (v : ι → E)
    {s t : Finset ι} (hs : s.Nonempty) (hst : s ⊆ t)
    (n : ℕ) (hcard : t.card ≤ n + 1) (D : ℝ) (hD0 : 0 ≤ D)
    (hD : ∀ i ∈ t, ∀ j ∈ t, dist (v i) (v j) ≤ D) :
    dist (faceCenter v s) (faceCenter v t) ≤
      ((n : ℝ) / (n + 1)) * D := by
  apply (dist_faceCenter_nested_le v hs hst D hD).trans
  apply mul_le_mul_of_nonneg_right _ hD0
  have htpos : (0 : ℝ) < t.card := by exact_mod_cast (hs.mono hst).card_pos
  have hsone : (1 : ℝ) ≤ s.card := by exact_mod_cast hs.card_pos
  have htcard : (t.card : ℝ) ≤ n + 1 := by exact_mod_cast hcard
  have hn : (0 : ℝ) < n + 1 := by positivity
  rw [Nat.cast_sub (Finset.card_le_card hst)]
  apply (div_le_div_iff₀ htpos hn).2
  nlinarith

lemma dist_faceCenter_of_mem_convexHull_le_mesh [DecidableEq ι] (v : ι → E)
    {t : Finset ι} (_ht : t.Nonempty) (n : ℕ) (hcard : t.card ≤ n + 1)
    (D : ℝ) (hD0 : 0 ≤ D)
    (hD : ∀ i ∈ t, ∀ j ∈ t, dist (v i) (v j) ≤ D)
    {x : E} (hx : x ∈ convexHull ℝ (v '' (t : Set ι))) :
    dist (faceCenter v t) x ≤ ((n : ℝ) / (n + 1)) * D := by
  obtain ⟨y, ⟨i, hi, rfl⟩, hy⟩ := convexHull_exists_dist_ge hx (faceCenter v t)
  rw [dist_comm] at hy
  apply hy.trans
  have hsingle : faceCenter v {i} = v i := by
    simp [faceCenter, Finset.centerMass]
  rw [← hsingle]
  exact dist_faceCenter_nested_le_mesh v (Finset.singleton_nonempty i)
    (Finset.singleton_subset_iff.mpr hi) n hcard D hD0 hD

end Problem340.SimplexSubdivision

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SingularSimplexLebesgue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Filter
open scoped Topology

namespace Problem340.SingularSimplexLebesgue

variable {D X I : Type*} [PseudoMetricSpace D] [CompactSpace D]
  [TopologicalSpace X]

theorem exists_small_image_radius (f : C(D, X)) (U : I → Set X)
    (hopen : ∀ i, IsOpen (U i)) (hcover : range f ⊆ ⋃ i, U i) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : Set D, s.Nonempty →
      (∀ x ∈ s, ∀ y ∈ s, dist x y < δ) →
      ∃ i, f '' s ⊆ U i := by
  have hpre : (univ : Set D) ⊆ ⋃ i, f ⁻¹' U i := by
    intro x _
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover (mem_range_self x))
    exact mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric
    isCompact_univ (fun i => (hopen i).preimage f.continuous) hpre
  refine ⟨δ, hδ, ?_⟩
  intro s hs hsmall
  obtain ⟨x, hx⟩ := hs
  obtain ⟨i, hi⟩ := hball x (mem_univ x)
  refine ⟨i, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  exact hi (show y ∈ Metric.ball x δ from hsmall y hy x hx)

theorem exists_finite_small_image_radius (S : Finset C(D, X)) (U : I → Set X)
    (hopen : ∀ i, IsOpen (U i))
    (hcover : ∀ f ∈ S, range f ⊆ ⋃ i, U i) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ f ∈ S, ∀ s : Set D, s.Nonempty →
      (∀ x ∈ s, ∀ y ∈ s, dist x y < δ) →
      ∃ i, f '' s ⊆ U i := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      exact ⟨1, zero_lt_one, by simp⟩
  | @insert f S hf ih =>
      obtain ⟨δf, hδf, hsmallf⟩ := exists_small_image_radius f U hopen
        (hcover f (Finset.mem_insert_self f S))
      obtain ⟨δS, hδS, hsmallS⟩ := ih (fun g hg => hcover g (Finset.mem_insert_of_mem hg))
      refine ⟨min δf δS, lt_min hδf hδS, ?_⟩
      intro g hg s hs hsmall
      rcases Finset.mem_insert.mp hg with rfl | hg
      · exact hsmallf s hs (fun x hx y hy =>
          lt_of_lt_of_le (hsmall x hx y hy) (min_le_left _ _))
      · exact hsmallS g hg s hs (fun x hx y hy =>
          lt_of_lt_of_le (hsmall x hx y hy) (min_le_right _ _))

theorem exists_finite_reparametrization_radius (S : Finset C(D, X)) (U : I → Set X)
    (hopen : ∀ i, IsOpen (U i))
    (hcover : ∀ f ∈ S, range f ⊆ ⋃ i, U i) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ f ∈ S, ∀ {A : Type*} [Nonempty A] (ρ : A → D),
      (∀ x y, dist (ρ x) (ρ y) < δ) →
      ∃ i, range (f ∘ ρ) ⊆ U i := by
  obtain ⟨δ, hδ, hsmall⟩ := exists_finite_small_image_radius S U hopen hcover
  refine ⟨δ, hδ, ?_⟩
  intro f hf A _ ρ hρ
  obtain ⟨i, hi⟩ := hsmall f hf (range ρ) (range_nonempty ρ) (by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    exact hρ x y)
  exact ⟨i, by simpa only [range_comp] using hi⟩

end Problem340.SingularSimplexLebesgue

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SimplexSubtypeMesh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Filter
open scoped Topology

namespace Problem340.SimplexSubtypeMesh

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem dist_le_of_convex_carrier {ι A : Type*} {s : Set E}
    (v : ι → E) (ρ : A → s) (D : ℝ)
    (hvertices : ∀ i j, dist (v i) (v j) ≤ D)
    (hcarrier : ∀ a, (ρ a).val ∈ convexHull ℝ (range v))
    (a b : A) : dist (ρ a) (ρ b) ≤ D := by
  obtain ⟨x, ⟨i, rfl⟩, y, ⟨j, rfl⟩, h⟩ :=
    convexHull_exists_dist_ge2 (hcarrier a) (hcarrier b)
  exact h.trans (hvertices i j)

open CategoryTheory Opposite
open scoped Simplicial

end Problem340.SimplexSubtypeMesh

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.RecursiveSubdivisionMesh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric

namespace Problem340.SimplexSubdivision

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma meshRatio_monotone_step (n : ℕ) :
    (n : ℝ) / (n + 1) ≤ (n + 1) / (n + 2) := by
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  nlinarith

theorem BarycentricCell.carrier_and_mesh {n : ℕ} {v w : Fin (n + 1) → E}
    (h : BarycentricCell n v w) (D : ℝ) (hD0 : 0 ≤ D)
    (hD : ∀ i j, dist (v i) (v j) ≤ D) :
    Set.range w ⊆ convexHull ℝ (Set.range v) ∧
      ∀ i j, dist (w i) (w j) ≤ ((n : ℝ) / (n + 1)) * D := by
  induction n with
  | zero =>
      change w = v at h
      subst w
      refine ⟨subset_convexHull ℝ _, ?_⟩
      intro i j
      have hij : i = j := Fin.ext (by omega)
      simp [hij]
  | succ n ih =>
      obtain ⟨i, u, hu, rfl⟩ := h
      obtain ⟨hcarrier, hmesh⟩ := ih hu (fun j k => hD _ _)
      have hface : Set.range (v ∘ i.succAbove) ⊆ Set.range v := by
        rintro _ ⟨j, rfl⟩
        exact ⟨i.succAbove j, rfl⟩
      have hchild : Set.range u ⊆ convexHull ℝ (Set.range v) :=
        hcarrier.trans (convexHull_mono hface)
      have hcenter : faceCenter v Finset.univ ∈ convexHull ℝ (Set.range v) := by
        simpa only [Finset.coe_univ, Set.image_univ] using
          faceCenter_mem_convexHull v (Finset.univ_nonempty : (Finset.univ : Finset (Fin (n + 2))).Nonempty)
      have hrad (j : Fin (n + 1)) :
          dist (faceCenter v Finset.univ) (u j) ≤
            (((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) + 1)) * D := by
        apply dist_faceCenter_of_mem_convexHull_le_mesh v Finset.univ_nonempty
          (n + 1) (by simp) D hD0 (fun a _ b _ => hD a b)
        simpa only [Finset.coe_univ, Set.image_univ] using hchild (Set.mem_range_self j)
      refine ⟨?_, ?_⟩
      · rintro _ ⟨j, rfl⟩
        refine Fin.cases ?_ (fun k => ?_) j
        · exact hcenter
        · exact hchild (Set.mem_range_self k)
      · intro j k
        refine Fin.cases ?_ (fun j => ?_) j
        · refine Fin.cases ?_ (fun k => ?_) k
          · simp only [Fin.cons_zero, dist_self]
            positivity
          · simpa only [Fin.cons_zero, Fin.cons_succ] using hrad k
        · refine Fin.cases ?_ (fun k => ?_) k
          · simpa only [Fin.cons_zero, Fin.cons_succ, dist_comm] using hrad j
          · simp only [Fin.cons_succ]
            apply (hmesh j k).trans
            apply mul_le_mul_of_nonneg_right _ hD0
            simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using
              meshRatio_monotone_step n

end Problem340.SimplexSubdivision

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SubdivisionSupportMesh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.SingularSubdivision

open SimplexSubdivision

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private lemma mem_support_linearCombination {α β : Type*}
    (v : α → β →₀ ℝ) (c : α →₀ ℝ) {q : β}
    (h : q ∈ (Finsupp.linearCombination ℝ v c).support) :
    ∃ p ∈ c.support, q ∈ (v p).support := by
  classical
  rw [Finsupp.linearCombination_apply, Finsupp.sum] at h
  obtain ⟨p, hp, hq⟩ := Finsupp.mem_support_finsetSum q h
  exact ⟨p, hp, Finsupp.support_smul hq⟩

lemma mem_support_cone {V : Type*} (a : V) (n : ℕ) (c : Chains V n)
    {q : Fin (n + 1) → V} (h : q ∈ (cone a n c).support) :
    ∃ p ∈ c.support, q = Fin.cons a p := by
  obtain ⟨p, hp, hq⟩ := mem_support_linearCombination
    (fun p => generator (Fin.cons a p)) c h
  refine ⟨p, hp, ?_⟩
  simpa [generator] using hq

theorem subdivision_support_barycentricCell {n : ℕ} (v : Fin (n + 1) → E)
    {w : Fin (n + 1) → E}
    (h : w ∈ (subdivision barycentricCenters (n + 1) (generator v)).support) :
    BarycentricCell n v w := by
  classical
  induction n with
  | zero =>
      rw [subdivision_barycentric_one] at h
      change w = v
      simpa [generator] using h
  | succ n ih =>
      rw [subdivision_generator] at h
      obtain ⟨u, hu, rfl⟩ := mem_support_cone _ _ _ h
      rw [boundary_generator, map_sum] at hu
      obtain ⟨i, _, hi⟩ := Finsupp.mem_support_finsetSum u hu
      rw [map_smul] at hi
      have hu' := Finsupp.support_smul hi
      exact ⟨i, u, ih _ hu', rfl⟩

end Problem340.SingularSubdivision

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SubdivisionSubtypeMesh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.SingularSubdivision

open SimplexSubdivision

lemma mapVertices_eq_mapDomain {V W : Type*} (f : V → W) (n : ℕ) (c : Chains V n) :
    mapVertices f n c = c.mapDomain (fun p => f ∘ p) := by
  classical
  simp [mapVertices, Finsupp.linearCombination_apply, Finsupp.mapDomain, generator,
    Finsupp.sum]

lemma mem_support_mapVertices_iff_of_injective {V W : Type*} (f : V → W)
    (hf : Function.Injective f) (n : ℕ) (c : Chains V n) (p : Fin n → V) :
    f ∘ p ∈ (mapVertices f n c).support ↔ p ∈ c.support := by
  rw [mapVertices_eq_mapDomain, Finsupp.mem_support_iff, Finsupp.mapDomain_apply,
    Finsupp.mem_support_iff]
  intro p q hpq
  funext i
  exact hf (congrFun hpq i)

lemma coe_simplexCenters (k n : ℕ) (v : Fin (n + 1) → StandardSimplex k) :
    ((simplexCenters k n v) : Fin (k + 1) → ℝ) =
      barycentricCenters n (fun i => (v i : Fin (k + 1) → ℝ)) := by
  change (AffineSimplex.simplexBarycenter v : Fin (k + 1) → ℝ) = _
  rw [AffineSimplex.simplexBarycenter_coe]
  change AffineSimplex.barycenter (fun i => (v i : Fin (k + 1) → ℝ)) =
    faceCenter (fun i => (v i : Fin (k + 1) → ℝ)) Finset.univ
  rw [AffineSimplex.barycenter_eq_sum, faceCenter_eq]
  simp

lemma coe_subdivision (k n : ℕ) (c : Chains (StandardSimplex k) n) :
    mapVertices RealSimplex.coordinates n (subdivision (simplexCenters k) n c) =
      subdivision barycentricCenters n (mapVertices RealSimplex.coordinates n c) :=
  mapVertices_subdivision RealSimplex.coordinates (simplexCenters k) barycentricCenters
    (coe_simplexCenters k) n c

lemma coe_subdivision_iterate (k n r : ℕ) (c : Chains (StandardSimplex k) n) :
    mapVertices RealSimplex.coordinates n (((subdivision (simplexCenters k) n)^[r]) c) =
      ((subdivision barycentricCenters n)^[r]) (mapVertices RealSimplex.coordinates n c) := by
  induction r with
  | zero => rfl
  | succ r ih =>
      rw [Function.iterate_succ_apply', coe_subdivision, ih,
        Function.iterate_succ_apply']

theorem simplex_iterated_subdivision_support {k n r : ℕ}
    (v : Fin n → StandardSimplex k) {w : Fin n → StandardSimplex k}
    (h : w ∈ (((subdivision (simplexCenters k) n)^[r]) (generator v)).support) :
    (fun i => (w i : Fin (k + 1) → ℝ)) ∈
      (((subdivision barycentricCenters n)^[r])
        (generator (fun i => (v i : Fin (k + 1) → ℝ)))).support := by
  have hc := (mem_support_mapVertices_iff_of_injective RealSimplex.coordinates
    RealSimplex.coordinates_injective n _ w).2 h
  rw [coe_subdivision_iterate, mapVertices_generator] at hc
  exact hc

end Problem340.SingularSubdivision

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.IteratedSubdivisionMesh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set

namespace Problem340.SingularSubdivision

lemma mem_support_linearMap {α β : Type*}
    (L : (α →₀ ℝ) →ₗ[ℝ] (β →₀ ℝ)) (c : α →₀ ℝ) {q : β}
    (h : q ∈ (L c).support) :
    ∃ p ∈ c.support, q ∈ (L (Finsupp.single p 1)).support := by
  classical
  have hL : L = Finsupp.linearCombination ℝ (fun p => L (Finsupp.single p 1)) := by
    apply Finsupp.lhom_ext
    intro p r
    simp only [Finsupp.linearCombination_single]
    have hr : Finsupp.single p r = r • Finsupp.single p 1 := by simp
    rw [hr, map_smul]
  rw [hL, Finsupp.linearCombination_apply, Finsupp.sum] at h
  obtain ⟨p, hp, hq⟩ := Finsupp.mem_support_finsetSum q h
  exact ⟨p, hp, Finsupp.support_smul hq⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem iterate_subdivision_support_carrier_and_mesh {n : ℕ}
    (v : Fin (n + 1) → E) (D : ℝ) (hD : 0 ≤ D)
    (hvertices : ∀ i j, dist (v i) (v j) ≤ D)
    (k : ℕ) {w : Fin (n + 1) → E}
    (h : w ∈ ((subdivision barycentricCenters (n + 1))^[k] (generator v)).support) :
    range w ⊆ convexHull ℝ (range v) ∧
      ∀ i j, dist (w i) (w j) ≤ ((n : ℝ) / (n + 1)) ^ k * D := by
  induction k generalizing w with
  | zero =>
      have hw : w = v := by simpa [generator] using h
      subst w
      exact ⟨subset_convexHull ℝ _, by simpa using hvertices⟩
  | succ k ih =>
      rw [Function.iterate_succ_apply'] at h
      obtain ⟨u, hu, hw⟩ := mem_support_linearMap _ _ h
      obtain ⟨huc, hum⟩ := ih hu
      obtain ⟨hwc, hwm⟩ := (subdivision_support_barycentricCell u hw).carrier_and_mesh
        (((n : ℝ) / (n + 1)) ^ k * D) (by positivity) hum
      refine ⟨hwc.trans ?_, ?_⟩
      · exact convexHull_min huc (convex_convexHull ℝ _)
      · intro i j
        calc
          dist (w i) (w j) ≤ (n : ℝ) / (n + 1) *
              (((n : ℝ) / (n + 1)) ^ k * D) := hwm i j
          _ = ((n : ℝ) / (n + 1)) ^ (k + 1) * D := by ring

theorem iterate_subdivision_support_mesh {n : ℕ}
    (v : Fin (n + 1) → E) (D : ℝ) (hD : 0 ≤ D)
    (hvertices : ∀ i j, dist (v i) (v j) ≤ D)
    (k : ℕ) {w : Fin (n + 1) → E}
    (h : w ∈ ((subdivision barycentricCenters (n + 1))^[k] (generator v)).support)
    (i j : Fin (n + 1)) :
    dist (w i) (w j) ≤ ((n : ℝ) / (n + 1)) ^ k * D :=
  (iterate_subdivision_support_carrier_and_mesh v D hD hvertices k h).2 i j

theorem simplex_iterate_subdivision_support_mesh {m n : ℕ}
    (v : Fin (n + 1) → StandardSimplex m) (D : ℝ) (hD : 0 ≤ D)
    (hvertices : ∀ i j, dist (v i) (v j) ≤ D)
    (k : ℕ) {w : Fin (n + 1) → StandardSimplex m}
    (h : w ∈ ((subdivision (simplexCenters m) (n + 1))^[k] (generator v)).support)
    (i j : Fin (n + 1)) :
    dist (w i) (w j) ≤ ((n : ℝ) / (n + 1)) ^ k * D :=
  iterate_subdivision_support_mesh (fun a => RealSimplex.coordinates (v a)) D hD hvertices k
    (simplex_iterated_subdivision_support v h) i j

theorem simplex_iterate_subdivision_realize_dist {m n : ℕ}
    (v : Fin (n + 1) → StandardSimplex m) (D : ℝ) (hD : 0 ≤ D)
    (hvertices : ∀ i j, dist (v i) (v j) ≤ D)
    (k : ℕ) {w : Fin (n + 1) → StandardSimplex m}
    (h : w ∈ ((subdivision (simplexCenters m) (n + 1))^[k] (generator v)).support)
    (x y : StandardSimplex n) :
    dist (AffineSimplex.simplexRealizeMap w x) (AffineSimplex.simplexRealizeMap w y) ≤
      ((n : ℝ) / (n + 1)) ^ k * D := by
  apply SimplexSubtypeMesh.dist_le_of_convex_carrier (fun i => RealSimplex.coordinates (w i))
    (fun point => RealSimplex.coordinateHomeomorph (AffineSimplex.simplexRealizeMap w point))
    _ _ _ x y
  · exact simplex_iterate_subdivision_support_mesh v D hD hvertices k h
  · intro a
    simpa only [RealSimplex.coordinateHomeomorph_apply, RealSimplex.coordinates,
      AffineSimplex.simplexRealizeMap_coe] using
      AffineSimplex.realize_mem_convexHull (fun i => RealSimplex.coordinates (w i)) a

theorem standardVertices_dist_le_one (n : ℕ) (i j : Fin (n + 1)) :
    dist (standardVertices n i) (standardVertices n j) ≤ 1 := by
  exact (Metric.dist_le_diam_of_mem
    (SStd.isBounded_range_toFun_comp_weights (Fin (n + 1)))
    (mem_range_self (standardVertices n i)) (mem_range_self (standardVertices n j))).trans
      (SStd.diam_range_toFun_comp_weights_subset_closedBall (Fin (n + 1)))

open Filter
open scoped Topology

theorem exists_iterated_subdivision_small_images
    {X I : Type} [TopologicalSpace X] (n : ℕ)
    (S : Finset C(StandardSimplex n, X)) (U : I → Set X)
    (hopen : ∀ i, IsOpen (U i)) (hcover : (univ : Set X) ⊆ ⋃ i, U i) :
    ∃ N : ℕ, ∀ k ≥ N, ∀ σ ∈ S,
      ∀ w ∈ ((subdivision (simplexCenters n) (n + 1))^[k]
        (generator (standardVertices n))).support,
      ∃ i, range (σ.comp (AffineSimplex.simplexRealizeMap w)) ⊆ U i := by
  obtain ⟨δ, hδ, hsmall⟩ := SingularSimplexLebesgue.exists_finite_reparametrization_radius
    S U hopen (fun _ _ => subset_trans (subset_univ _) hcover)
  have hr0 : (0 : ℝ) ≤ (n : ℝ) / (n + 1) := by positivity
  have hr1 : (n : ℝ) / (n + 1) < 1 := by
    apply (div_lt_one (by positivity)).2
    linarith
  have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hδ))
  refine ⟨N, ?_⟩
  intro k hk σ hσ w hw
  apply hsmall σ hσ (AffineSimplex.simplexRealizeMap w)
  intro x y
  have hdist := simplex_iterate_subdivision_realize_dist (standardVertices n) 1
    zero_le_one (standardVertices_dist_le_one n) k hw x y
  exact hdist.trans_lt (by simpa only [mul_one] using hN k hk)

end Problem340.SingularSubdivision

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SingularSmallChainSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

namespace Problem340

theorem simplicialChainMap_finsupp {S T : SSet} (f : S ⟶ T) (n : ℕ)
    (z : S _⦋n⦌ →₀ ℝ) :
    ((SSet.chainComplexMap f (ModuleCat.of ℝ ℝ)).f n).hom
      (simplicialChainsFinsuppEquiv S n z) =
    simplicialChainsFinsuppEquiv T n
      (Finsupp.lmapDomain ℝ ℝ (f.app (op ⦋n⦌)) z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single σ r =>
    simp only [simplicialChainsFinsuppEquiv_single, Finsupp.lmapDomain_apply,
      Finsupp.mapDomain_single]
    exact congrArg (fun k : ModuleCat.of ℝ ℝ ⟶
      (T.chainComplex (ModuleCat.of ℝ ℝ)).X n => k.hom r)
      (SSet.ι_chainComplexMap_f S T f (ModuleCat.of ℝ ℝ) σ)

theorem finsupp_range_lmapDomain_eq_supported {α β : Type*} (f : α → β) :
    LinearMap.range (Finsupp.lmapDomain ℝ ℝ f) =
      Finsupp.supported ℝ ℝ (Set.range f) := by
  simpa only [Finsupp.supported_univ, Submodule.map_top, Set.image_univ] using
    (Finsupp.lmapDomain_supported ℝ ℝ f (Set.univ : Set α))

theorem mem_range_simplicialChainMap_iff {S T : SSet} (f : S ⟶ T) (n : ℕ)
    (z : (T.chainComplex (ModuleCat.of ℝ ℝ)).X n) :
    z ∈ LinearMap.range ((SSet.chainComplexMap f (ModuleCat.of ℝ ℝ)).f n).hom ↔
      (simplicialChainsFinsuppEquiv T n).symm z ∈
        Finsupp.supported ℝ ℝ (Set.range (f.app (op ⦋n⦌))) := by
  rw [← finsupp_range_lmapDomain_eq_supported]
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨v, rfl⟩ := (simplicialChainsFinsuppEquiv S n).surjective w
    refine ⟨v, ?_⟩
    rw [simplicialChainMap_finsupp, LinearEquiv.symm_apply_apply]
  · rintro ⟨v, hv⟩
    refine ⟨simplicialChainsFinsuppEquiv S n v, ?_⟩
    rw [simplicialChainMap_finsupp, hv, LinearEquiv.apply_symm_apply]

theorem mem_range_subcomplex_chainMap_iff (S : SSet) (K : S.Subcomplex) (n : ℕ)
    (z : (S.chainComplex (ModuleCat.of ℝ ℝ)).X n) :
    z ∈ LinearMap.range ((SSet.chainComplexMap K.ι (ModuleCat.of ℝ ℝ)).f n).hom ↔
      (simplicialChainsFinsuppEquiv S n).symm z ∈
        Finsupp.supported ℝ ℝ (K.obj (op ⦋n⦌)) := by
  rw [mem_range_simplicialChainMap_iff]
  change _ ∈ Finsupp.supported ℝ ℝ (Set.range (Subtype.val : K.obj (op ⦋n⦌) → S _⦋n⦌)) ↔ _
  rw [Subtype.range_val]

theorem finsupp_domLCongr_mem_supported_iff {α β : Type*} (e : α ≃ β)
    (z : α →₀ ℝ) (t : Set β) :
    (Finsupp.domLCongr e : (α →₀ ℝ) ≃ₗ[ℝ] (β →₀ ℝ)) z ∈
      Finsupp.supported ℝ ℝ t ↔
    z ∈ Finsupp.supported ℝ ℝ (e ⁻¹' t) := by
  rw [Finsupp.mem_supported', Finsupp.mem_supported']
  constructor
  · intro h a ha
    have hh := h (e a) ha
    simpa using hh
  · intro h b hb
    have hh := h (e.symm b) (by simpa using hb)
    simpa using hh

theorem mem_range_singularSubcomplex_iff {X : Type} [TopologicalSpace X]
    (K : (TopCat.toSSet.obj (TopCat.of X)).Subcomplex) (n : ℕ)
    (z : (realSingularChainComplex X).X n) :
    z ∈ LinearMap.range ((SSet.chainComplexMap K.ι (ModuleCat.of ℝ ℝ)).f n).hom ↔
      (singularChainsFinsuppEquiv X n).symm z ∈
        Finsupp.supported ℝ ℝ (Set.ofPred (fun σ : RealSingularSimplex X n =>
          (TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋n⦌)).symm σ ∈ K.obj (op ⦋n⦌))) := by
  refine (mem_range_subcomplex_chainMap_iff _ K n z).trans ?_
  change _ ↔ Finsupp.domLCongr (R := ℝ) (TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋n⦌))
    ((simplicialChainsFinsuppEquiv (TopCat.toSSet.obj (TopCat.of X)) n).symm z) ∈ _
  rw [finsupp_domLCongr_mem_supported_iff]
  simp only [Set.preimage_ofPred_eq, Equiv.symm_apply_apply]
  rfl

namespace SingularSmallChains

theorem mem_range_inclusion_iff_supported {X : Type} [TopologicalSpace X]
    {ι : Type*} (U : ι → Set X) (n : ℕ)
    (z : (realSingularChainComplex X).X n) :
    z ∈ LinearMap.range ((inclusion U).f n).hom ↔
      (singularChainsFinsuppEquiv X n).symm z ∈
        Finsupp.supported ℝ ℝ (Set.ofPred (fun σ : RealSingularSimplex X n =>
          ∃ i, Set.range σ ⊆ U i)) := by
  refine (mem_range_singularSubcomplex_iff (small U) n z).trans ?_
  simp only [mem_small, Equiv.apply_symm_apply]

end SingularSmallChains

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SingularRealizedSmallness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.SingularSmallChains

open SingularSubdivision

variable {X : Type} [TopologicalSpace X] {ι : Type*}

theorem simplexChain_mem_range_inclusion (U : ι → Set X) {n : ℕ}
    (σ : RealSingularSimplex X n) (hσ : ∃ i, Set.range σ ⊆ U i) :
    SingularChainFormulas.simplexChain σ ∈ LinearMap.range ((inclusion U).f n).hom := by
  apply (mem_range_inclusion_iff_supported U n _).mpr
  change (singularChainsFinsuppEquiv X n).symm (realSingularGenerator σ 1) ∈ _
  rw [← singularChainsFinsuppEquiv_single X n σ 1, LinearEquiv.symm_apply_apply]
  exact Finsupp.single_mem_supported ℝ 1 hσ

theorem pushforward_realize_mem_range_inclusion (U : ι → Set X) (k n : ℕ)
    (σ : C(StandardSimplex k, X)) (c : Chains (StandardSimplex k) (n + 1))
    (hc : ∀ w ∈ c.support,
      ∃ i, Set.range (σ.comp (AffineSimplex.simplexRealizeMap w)) ⊆ U i) :
    ((realSingularChainMap σ σ.continuous).f n).hom
      (SimplexSingularRealization.realize k n c) ∈
        LinearMap.range ((inclusion U).f n).hom := by
  classical
  rw [SimplexSingularRealization.realize, Finsupp.linearCombination_apply,
    Finsupp.sum, map_sum]
  apply (LinearMap.range ((inclusion U).f n).hom).sum_mem
  intro w hw
  rw [map_smul, SingularChainFormulas.simplexChain_map]
  exact (LinearMap.range ((inclusion U).f n).hom).smul_mem _
    (simplexChain_mem_range_inclusion U _ (hc w hw))

theorem exists_iterated_realize_mem_range_inclusion {I : Type}
    (U : I → Set X) (hopen : ∀ i, IsOpen (U i))
    (hcover : (Set.univ : Set X) ⊆ ⋃ i, U i)
    (n : ℕ) (σ : RealSingularSimplex X n) :
    ∃ N : ℕ, ∀ k ≥ N,
      ((realSingularChainMap σ σ.continuous).f n).hom
        (SimplexSingularRealization.realize n n
          ((subdivision (simplexCenters n) (n + 1))^[k]
            (generator (standardVertices n)))) ∈
          LinearMap.range ((inclusion U).f n).hom := by
  classical
  obtain ⟨N, hN⟩ := exists_iterated_subdivision_small_images n {σ} U hopen hcover
  refine ⟨N, fun k hk => ?_⟩
  apply pushforward_realize_mem_range_inclusion U n n σ
  exact hN k hk σ (Finset.mem_singleton_self σ)

end Problem340.SingularSmallChains

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SingularSubdivisionIterateRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option backward.isDefEq.respectTransparency false

namespace OAI

noncomputable section

open CategoryTheory

namespace Problem340.SingularSubdivisionIterateRealization

open SingularSubdivision SingularUniversalOperator SimplexSingularRealization

theorem operator_realize (k n : ℕ) (c : Chains (Simplex k) (n + 1)) :
    ((degreeOperator n).app (TopCat.of (Simplex k))).hom (realize k n c) =
      realize k n (subdivision (simplexCenters k) (n + 1) c) := by
  have h : ((degreeOperator n).app (TopCat.of (Simplex k))).hom.comp (realize k n) =
      (realize k n).comp (subdivision (simplexCenters k) (n + 1)) := by
    apply linearMap_ext
    intro v
    change ((degreeOperator n).app (TopCat.of (Simplex k))).hom
      (realize k n (generator v)) = realize k n
        (subdivision (simplexCenters k) (n + 1) (generator v))
    rw [realize_generator]
    change ((degreeOperator n).app (TopCat.of (Simplex k))).hom
      (realSingularGenerator (AffineSimplex.simplexRealizeMap v) 1) = _
    rw [operator_realSingularGenerator, one_smul, affineMap_realize]
    congr 1
    rw [universalSubdivision,
      mapVertices_subdivision _ _ _ (affine_centers v), mapVertices_generator]
    congr 2
    funext i
    exact AffineSimplex.simplexRealizeMap_vertex v i
  exact LinearMap.congr_fun h c

theorem operator_pushforward {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (n : ℕ) (f : C(X, Y)) (c : (realSingularChainComplex X).X n) :
    ((degreeOperator n).app (TopCat.of Y)).hom
      (((realSingularChainMap f f.continuous).f n).hom c) =
      ((realSingularChainMap f f.continuous).f n).hom
        (((degreeOperator n).app (TopCat.of X)).hom c) := by
  exact congrArg (fun g : (chainsFunctor n).obj (TopCat.of X) ⟶
      (chainsFunctor n).obj (TopCat.of Y) => g.hom c)
    ((degreeOperator n).naturality (TopCat.ofHom f))

theorem iterate_pushforward_realize {X : Type} [TopologicalSpace X]
    (k n r : ℕ) (f : C(Simplex k, X)) (c : Chains (Simplex k) (n + 1)) :
    ((((degreeOperator n).app (TopCat.of X)).hom)^[r])
      (((realSingularChainMap f f.continuous).f n).hom (realize k n c)) =
      ((realSingularChainMap f f.continuous).f n).hom
        (realize k n (((subdivision (simplexCenters k) (n + 1))^[r]) c)) := by
  induction r with
  | zero => rfl
  | succ r ih =>
      rw [Function.iterate_succ_apply', ih, operator_pushforward,
        operator_realize, Function.iterate_succ_apply']

theorem iterate_simplexChain {X : Type} [TopologicalSpace X]
    (n r : ℕ) (σ : C(Simplex n, X)) :
    ((((degreeOperator n).app (TopCat.of X)).hom)^[r])
      (SingularChainFormulas.simplexChain σ) =
      ((realSingularChainMap σ σ.continuous).f n).hom
        (realize n n (((subdivision (simplexCenters n) (n + 1))^[r])
          (generator (standardVertices n)))) := by
  have h := iterate_pushforward_realize n n r σ (generator (standardVertices n))
  rw [realize_standardVertices, SingularChainFormulas.simplexChain_map] at h
  simpa only [ContinuousMap.comp_id] using h

end Problem340.SingularSubdivisionIterateRealization

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.IteratedSubdivision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory

namespace Problem340.IteratedSubdivision

section Linear

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

theorem pow_mem_of_mem (s : Module.End R M) (P : Submodule R M)
    (hP : ∀ x ∈ P, s x ∈ P) {x : M} (hx : x ∈ P) (n : ℕ) :
    (s ^ n) x ∈ P := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    simpa only [pow_succ', Module.End.mul_apply] using hP ((s ^ n) x) ih

theorem mem_eventuallyIn_of_pow_mem (s : Module.End R M) (P : Submodule R M)
    (hP : ∀ x ∈ P, s x ∈ P) {x : M} {N : ℕ} (hx : (s ^ N) x ∈ P) :
    x ∈ eventuallyIn s P := by
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm N k]
  simpa only [pow_add, Module.End.mul_apply] using
    pow_mem_of_mem s P hP hx k

end Linear

section ChainHomotopy

variable {V : Type*} [Category V] [Preadditive V]
variable {ι : Type*} {c : ComplexShape ι} {C : HomologicalComplex V c}

theorem chainIterate_eq_pow (s : C ⟶ C) (n : ℕ) :
    chainIterate s n = End.asHom ((End.of s) ^ n) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [chainIterate, ih, pow_succ', End.mul_def]

end ChainHomotopy

section Support

variable {R : Type*} [Ring R] {ι : Type*} {c : ComplexShape ι}
variable {C : HomologicalComplex (ModuleCat R) c}

theorem chainIterate_f_hom (s : C ⟶ C) (n : ℕ) (i : ι) :
    ((chainIterate s n).f i).hom = ((s.f i).hom ^ n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    ext x
    simp only [chainIterate, HomologicalComplex.comp_f, ModuleCat.hom_comp,
      LinearMap.comp_apply, ih, pow_succ', Module.End.mul_apply]

end Support

end Problem340.IteratedSubdivision

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SingularSubdivisionSmallness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory

namespace Problem340.SingularSmallChains

variable {X : Type} [TopologicalSpace X] {ι : Type*}

theorem naturalChainMap_preserves_range (U : ι → Set X)
    (S : singularFunctor ⟶ singularFunctor) (n : ℕ)
    (z : (realSingularChainComplex X).X n)
    (hz : z ∈ LinearMap.range ((inclusion U).f n).hom) :
    ((S.app (TopCat.of X)).f n).hom z ∈ LinearMap.range ((inclusion U).f n).hom := by
  obtain ⟨w, rfl⟩ := hz
  refine ⟨((restrictChainMap U S).f n).hom w, ?_⟩
  exact congrArg (fun f : chains U ⟶ realSingularChainComplex X => (f.f n).hom w)
    (restrictChainMap_inclusion U S)

theorem eventually_mem_range_inclusion_of_generators (U : ι → Set X)
    (S : singularFunctor ⟶ singularFunctor) (n : ℕ)
    (hgen : ∀ σ : RealSingularSimplex X n, ∃ N : ℕ,
      (((S.app (TopCat.of X)).f n).hom ^ N) (realSingularGenerator σ 1) ∈
        LinearMap.range ((inclusion U).f n).hom)
    (z : (realSingularChainComplex X).X n) :
    ∃ N : ℕ, ∀ k, N ≤ k →
      (((S.app (TopCat.of X)).f n).hom ^ k) z ∈
        LinearMap.range ((inclusion U).f n).hom := by
  let s := ((S.app (TopCat.of X)).f n).hom
  let P := LinearMap.range ((inclusion U).f n).hom
  have hP : ∀ x ∈ P, s x ∈ P := naturalChainMap_preserves_range U S n
  have hg (σ : RealSingularSimplex X n) :
      realSingularGenerator σ 1 ∈ IteratedSubdivision.eventuallyIn s P := by
    obtain ⟨N, hN⟩ := hgen σ
    exact IteratedSubdivision.mem_eventuallyIn_of_pow_mem s P hP hN
  apply realSingularChain_induction (P := fun z => z ∈ IteratedSubdivision.eventuallyIn s P)
    (IteratedSubdivision.eventuallyIn s P).zero_mem
    (fun _ _ hx hy => (IteratedSubdivision.eventuallyIn s P).add_mem hx hy)
    (fun σ r => ?_) z
  have h := (IteratedSubdivision.eventuallyIn s P).smul_mem r (hg σ)
  simpa only [← map_smul, smul_eq_mul, mul_one] using h

theorem end_pow_f_hom (S : singularFunctor ⟶ singularFunctor) (n k : ℕ) :
    (((End.of (S.app (TopCat.of X)) ^ k).asHom).f n).hom =
      (((S.app (TopCat.of X)).f n).hom ^ k) := by
  rw [← IteratedSubdivision.chainIterate_eq_pow]
  exact IteratedSubdivision.chainIterate_f_hom _ _ _

theorem exists_pow_mem_range_inclusion_of_generators (U : ι → Set X)
    (S : singularFunctor ⟶ singularFunctor)
    (hgen : ∀ (n : ℕ) (σ : RealSingularSimplex X n), ∃ k : ℕ,
      (((End.of (S.app (TopCat.of X)) ^ k).asHom).f n).hom
        (realSingularGenerator σ 1) ∈ LinearMap.range ((inclusion U).f n).hom) :
    ∀ (n : ℕ) (z : (realSingularChainComplex X).X n), ∃ k : ℕ,
      (((End.of (S.app (TopCat.of X)) ^ k).asHom).f n).hom z ∈
        LinearMap.range ((inclusion U).f n).hom := by
  intro n z
  have hg (σ : RealSingularSimplex X n) : ∃ k : ℕ,
      (((S.app (TopCat.of X)).f n).hom ^ k) (realSingularGenerator σ 1) ∈
        LinearMap.range ((inclusion U).f n).hom := by
    simpa only [end_pow_f_hom] using hgen n σ
  obtain ⟨N, hN⟩ := eventually_mem_range_inclusion_of_generators U S n hg z
  exact ⟨N, by simpa only [end_pow_f_hom] using hN N le_rfl⟩

end Problem340.SingularSmallChains

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SingularSubdivisionEventuallySmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory

namespace Problem340.SingularSmallChains

variable {X : Type} [TopologicalSpace X]

theorem actualSubdivision_eq_degreeOperator (n : ℕ) :
    ActualSingularSubdivision.subdivision n =
      SingularSubdivisionIterateRealization.degreeOperator n := by
  unfold ActualSingularSubdivision.subdivision ActualSingularSubdivision.subdivisionChain
  rw [ActualSingularSubdivision.realize_eq_aux]

theorem actualSubdivision_pow_generator (n k : ℕ) (σ : RealSingularSimplex X n) :
    (((End.of (ActualSingularSubdivision.chainMap.app (TopCat.of X)) ^ k).asHom).f n).hom
      (realSingularGenerator σ 1) =
    ((realSingularChainMap σ σ.continuous).f n).hom
      (SimplexSingularRealization.realize n n
        ((SingularSubdivision.subdivision (SingularSubdivision.simplexCenters n) (n + 1))^[k]
          (SingularSubdivision.generator (SingularSubdivision.standardVertices n)))) := by
  rw [end_pow_f_hom, ActualSingularSubdivision.chainMap_app_f,
    Module.End.pow_apply, actualSubdivision_eq_degreeOperator]
  exact SingularSubdivisionIterateRealization.iterate_simplexChain n k σ

theorem exists_actualSubdivision_pow_mem_range {I : Type}
    (U : I → Set X) (hopen : ∀ i, IsOpen (U i))
    (hcover : (Set.univ : Set X) ⊆ ⋃ i, U i) :
    ∀ (n : ℕ) (z : (realSingularChainComplex X).X n), ∃ k : ℕ,
      (((End.of (ActualSingularSubdivision.chainMap.app (TopCat.of X)) ^ k).asHom).f n).hom z ∈
        LinearMap.range ((inclusion U).f n).hom := by
  apply exists_pow_mem_range_inclusion_of_generators U ActualSingularSubdivision.chainMap
  intro n σ
  obtain ⟨N, hN⟩ := exists_iterated_realize_mem_range_inclusion U hopen hcover n σ
  refine ⟨N, ?_⟩
  rw [actualSubdivision_pow_generator]
  exact hN N le_rfl

end Problem340.SingularSmallChains

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SingularCoverNaturality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

namespace Problem340.SingularCover

variable {X : Type} [TopologicalSpace X]

variable {K L : SSet} (f : K ⟶ L)
variable {A B : K.Subcomplex} {A' B' : L.Subcomplex}

theorem union_connecting_naturality
    (hA : A ≤ A'.preimage f) (hB : B ≤ B'.preimage f) (n : ℕ) :
    (unionShortComplex_shortExact A B).δ (n + 1) n (by simp) ≫
        HomologicalComplex.homologyMap (unionShortComplexMap f hA hB).τ₁ n =
      HomologicalComplex.homologyMap (unionShortComplexMap f hA hB).τ₃ (n + 1) ≫
        (unionShortComplex_shortExact A' B').δ (n + 1) n (by simp) := by
  exact HomologicalComplex.HomologySequence.δ_naturality
    (unionShortComplexMap f hA hB)
    (unionShortComplex_shortExact A B) (unionShortComplex_shortExact A' B')
    (n + 1) n (by simp)

end Problem340.SingularCover

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SingularSupportNaturality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

namespace Problem340

namespace SingularSmallChains

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem subspaceHomologyIso_naturality_apply
    (f : X → Y) (hf : Continuous f) (s : Set X) (t : Set Y)
    (hst : Set.MapsTo f s t) (n : ℕ) (v : RealSingularHomology n s) :
    (subspaceHomologyIso t n).toLinearEquiv
        (realHomologyMap n (restrictMap f hf s t hst)
          (restrictMap f hf s t hst).continuous v) =
      (SSet.homologyMap (mapInSubset f hf s t hst) (ModuleCat.of ℝ ℝ) n).hom
        ((subspaceHomologyIso s n).toLinearEquiv v) := by
  have h := congrArg (fun k => (SSet.homologyFunctor (ModuleCat.of ℝ ℝ) n).map k)
    (subspaceIso_naturality f hf s t hst)
  simp only [Functor.map_comp] at h
  exact congrArg (fun k : RealSingularHomology n s ⟶
      (inSubset t : SSet).homology (ModuleCat.of ℝ ℝ) n => k.hom v) h

end SingularSmallChains
end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SmallCoverNaturality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Problem340.SmallCoverMayerVietoris

open SingularSmallChains SingularCover

section SimplicialTransport

variable {K L : SSet}

theorem restrictedMap_eqToHom (f : K ⟶ L)
    {A B : K.Subcomplex} {A' B' : L.Subcomplex} (h : A = B) (h' : A' = B')
    (hA : A ≤ A'.preimage f) (hB : B ≤ B'.preimage f) :
    eqToHom (congrArg SSet.Subcomplex.toSSet h) ≫ restrictedMap f B B' hB =
      restrictedMap f A A' hA ≫ eqToHom (congrArg SSet.Subcomplex.toSSet h') := by
  subst B
  subst B'
  simp

end SimplicialTransport

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

@[reassoc] theorem smallUnionHomologyIso_naturality
    (f : X → Y) (hf : Continuous f) (U V : Set X) (U' V' : Set Y)
    (hU : Set.MapsTo f U U') (hV : Set.MapsTo f V V') (n : ℕ) :
    (smallUnionHomologyIso U V n).hom ≫
        SSet.homologyMap (restrictedMap (singularMap f hf)
          (inSubset U ⊔ inSubset V) (inSubset U' ⊔ inSubset V')
          (preserves_union (singularMap f hf)
            (inSubset_le_preimage f hf U U' hU) (inSubset_le_preimage f hf V V' hV)))
          (ModuleCat.of ℝ ℝ) n =
      SSet.homologyMap (binaryMap f hf U V U' V' hU hV) (ModuleCat.of ℝ ℝ) n ≫
        (smallUnionHomologyIso U' V' n).hom := by
  have h := (SSet.homologyFunctor (ModuleCat.of ℝ ℝ) n).congr_map
    (restrictedMap_eqToHom (singularMap f hf) (small_binaryCover U V)
      (small_binaryCover U' V') (binary_le_preimage f hf U V U' V' hU hV)
      (preserves_union (singularMap f hf)
        (inSubset_le_preimage f hf U U' hU) (inSubset_le_preimage f hf V V' hV)))
  dsimp only [SSet.homologyFunctor] at h
  simpa only [Functor.map_comp, SSet.homologyFunctor_map, SSet.homologyFunctor_obj,
    SSet.homologyMap_comp, smallUnionHomologyIso, Functor.mapIso_hom, eqToIso.hom,
    binaryMap] using h

theorem restrictedMap_inSubset (f : X → Y) (hf : Continuous f)
    (s : Set X) (t : Set Y) (h : Set.MapsTo f s t) :
    restrictedMap (singularMap f hf) (inSubset s) (inSubset t)
        (inSubset_le_preimage f hf s t h) = mapInSubset f hf s t h := rfl

@[reassoc] theorem subspaceHomologyIso_naturality
    (f : X → Y) (hf : Continuous f) (s : Set X) (t : Set Y)
    (h : Set.MapsTo f s t) (n : ℕ) :
    ModuleCat.ofHom (realHomologyMap n (restrictMap f hf s t h)
        (restrictMap f hf s t h).continuous) ≫ (subspaceHomologyIso t n).hom =
      (subspaceHomologyIso s n).hom ≫
        SSet.homologyMap (mapInSubset f hf s t h) (ModuleCat.of ℝ ℝ) n := by
  apply ModuleCat.hom_ext
  ext v
  exact subspaceHomologyIso_naturality_apply f hf s t h n v

@[reassoc] theorem intersectionHomologyIso_naturality
    (f : X → Y) (hf : Continuous f) (U V : Set X) (U' V' : Set Y)
    (hU : Set.MapsTo f U U') (hV : Set.MapsTo f V V') (n : ℕ) :
    ModuleCat.ofHom (realHomologyMap n (intersectionMap f hf U V U' V' hU hV)
        (intersectionMap f hf U V U' V' hU hV).continuous) ≫
        (intersectionHomologyIso U' V' n).hom =
      (intersectionHomologyIso U V n).hom ≫
        SSet.homologyMap (restrictedMap (singularMap f hf)
          (inSubset U ⊓ inSubset V) (inSubset U' ⊓ inSubset V')
          (preserves_inter (singularMap f hf)
            (inSubset_le_preimage f hf U U' hU) (inSubset_le_preimage f hf V V' hV)))
          (ModuleCat.of ℝ ℝ) n := by
  let hI : Set.MapsTo f (U ∩ V) (U' ∩ V') := fun _ hx => ⟨hU hx.1, hV hx.2⟩
  have heq := (SSet.homologyFunctor (ModuleCat.of ℝ ℝ) n).congr_map
    (restrictedMap_eqToHom (singularMap f hf) (inSubset_inter U V)
      (inSubset_inter U' V') (inSubset_le_preimage f hf (U ∩ V) (U' ∩ V') hI)
      (preserves_inter (singularMap f hf)
        (inSubset_le_preimage f hf U U' hU) (inSubset_le_preimage f hf V V' hV)))
  dsimp only [SSet.homologyFunctor] at heq
  simp only [SSet.homologyMap_comp] at heq
  change ModuleCat.ofHom (realHomologyMap n (restrictMap f hf (U ∩ V) (U' ∩ V') hI)
      (restrictMap f hf (U ∩ V) (U' ∩ V') hI).continuous) ≫
      ((subspaceHomologyIso (U' ∩ V') n).hom ≫
        SSet.homologyMap (eqToHom (congrArg SSet.Subcomplex.toSSet
          (inSubset_inter U' V'))) (ModuleCat.of ℝ ℝ) n) =
    ((subspaceHomologyIso (U ∩ V) n).hom ≫
      SSet.homologyMap (eqToHom (congrArg SSet.Subcomplex.toSSet
        (inSubset_inter U V))) (ModuleCat.of ℝ ℝ) n) ≫
      SSet.homologyMap (restrictedMap (singularMap f hf)
        (inSubset U ⊓ inSubset V) (inSubset U' ⊓ inSubset V')
        (preserves_inter (singularMap f hf)
          (inSubset_le_preimage f hf U U' hU) (inSubset_le_preimage f hf V V' hV)))
        (ModuleCat.of ℝ ℝ) n
  rw [← Category.assoc, subspaceHomologyIso_naturality f hf (U ∩ V) (U' ∩ V') hI n]
  rw [Category.assoc, ← restrictedMap_inSubset f hf (U ∩ V) (U' ∩ V') hI,
    ← heq, ← Category.assoc]

theorem transport_connecting_naturality {C : Type*} [Category C]
    {A A' B B' D D' E E' : C}
    (u : D ≅ A) (u' : D' ≅ A') (i : E ≅ B) (i' : E' ≅ B')
    (δ : A ⟶ B) (δ' : A' ⟶ B')
    (mA : A ⟶ A') (mB : B ⟶ B') (mD : D ⟶ D') (mE : E ⟶ E')
    (hu : u.hom ≫ mA = mD ≫ u'.hom)
    (hδ : δ ≫ mB = mA ≫ δ') (hi : mE ≫ i'.hom = i.hom ≫ mB) :
    mD ≫ (u'.hom ≫ δ' ≫ i'.inv) = (u.hom ≫ δ ≫ i.inv) ≫ mE := by
  apply (cancel_mono i'.hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hi]
  simp only [Iso.inv_hom_id_assoc]
  rw [hδ, ← Category.assoc, ← hu, Category.assoc]

@[reassoc] theorem connecting_naturality
    (f : X → Y) (hf : Continuous f) (U V : Set X) (U' V' : Set Y)
    (hU : Set.MapsTo f U U') (hV : Set.MapsTo f V V') (n : ℕ) :
    SSet.homologyMap (binaryMap f hf U V U' V' hU hV) (ModuleCat.of ℝ ℝ) (n + 1) ≫
        connecting U' V' n =
      connecting U V n ≫
        ModuleCat.ofHom (realHomologyMap n (intersectionMap f hf U V U' V' hU hV)
          (intersectionMap f hf U V U' V' hU hV).continuous) := by
  let hA := inSubset_le_preimage f hf U U' hU
  let hB := inSubset_le_preimage f hf V V' hV
  let mI := SSet.homologyMap (restrictedMap (singularMap f hf)
    (inSubset U ⊓ inSubset V) (inSubset U' ⊓ inSubset V')
    (preserves_inter (singularMap f hf) hA hB)) (ModuleCat.of ℝ ℝ) n
  let mU := SSet.homologyMap (restrictedMap (singularMap f hf)
    (inSubset U ⊔ inSubset V) (inSubset U' ⊔ inSubset V')
    (preserves_union (singularMap f hf) hA hB)) (ModuleCat.of ℝ ℝ) (n + 1)
  have hδ : SimplicialMayerVietoris.connecting (inSubset U) (inSubset V) n ≫ mI =
      mU ≫ SimplicialMayerVietoris.connecting (inSubset U') (inSubset V') n :=
    union_connecting_naturality (singularMap f hf) hA hB n
  exact transport_connecting_naturality
    (smallUnionHomologyIso U V (n + 1)) (smallUnionHomologyIso U' V' (n + 1))
    (intersectionHomologyIso U V n) (intersectionHomologyIso U' V' n)
    (SimplicialMayerVietoris.connecting (inSubset U) (inSubset V) n)
    (SimplicialMayerVietoris.connecting (inSubset U') (inSubset V') n)
    mU mI _ _
    (smallUnionHomologyIso_naturality f hf U V U' V' hU hV (n + 1)) hδ
    (intersectionHomologyIso_naturality f hf U V U' V' hU hV n)

theorem descend_connecting_naturality {C : Type*} [Category C]
    {A A' B B' D D' : C}
    (s : D ⟶ A) [Epi s] (s' : D' ⟶ A')
    (δ : A ⟶ B) (δ' : A' ⟶ B') (d : D ⟶ B) (d' : D' ⟶ B')
    (f : A ⟶ A') (g : D ⟶ D') (h : B ⟶ B')
    (hs : s ≫ f = g ≫ s') (hd : s ≫ δ = d) (hd' : s' ≫ δ' = d')
    (hn : g ≫ d' = d ≫ h) : f ≫ δ' = δ ≫ h := by
  apply (cancel_epi s).1
  rw [← Category.assoc, hs, Category.assoc, hd', hn, ← hd, Category.assoc]

@[reassoc] theorem singularConnectingIsoOfQuasiIsoAt_naturality
    (f : X → Y) (hf : Continuous f) (U V : Set X) (U' V' : Set Y)
    [ContractibleSpace U] [ContractibleSpace V]
    [ContractibleSpace U'] [ContractibleSpace V']
    (hU : Set.MapsTo f U U') (hV : Set.MapsTo f V V') (n : ℕ) (hn : n ≠ 0)
    [QuasiIsoAt (inclusion (binaryCover U V)) (n + 1)]
    [QuasiIsoAt (inclusion (binaryCover U' V')) (n + 1)] :
    ModuleCat.ofHom (realHomologyMap (n + 1) f hf) ≫
        (singularConnectingIsoOfQuasiIsoAt U' V' n hn).hom =
      (singularConnectingIsoOfQuasiIsoAt U V n hn).hom ≫
        ModuleCat.ofHom (realHomologyMap n (intersectionMap f hf U V U' V' hU hV)
          (intersectionMap f hf U V U' V' hU hV).continuous) := by
  exact descend_connecting_naturality
    (HomologicalComplex.homologyMap (inclusion (binaryCover U V)) (n + 1))
    (HomologicalComplex.homologyMap (inclusion (binaryCover U' V')) (n + 1))
    (singularConnectingIsoOfQuasiIsoAt U V n hn).hom
    (singularConnectingIsoOfQuasiIsoAt U' V' n hn).hom
    (connecting U V n) (connecting U' V' n) _ _ _
    (binaryHomologyMap_inclusion f hf U V U' V' hU hV (n + 1)).symm
    (inclusion_singularConnectingIsoOfQuasiIsoAt U V n hn)
    (inclusion_singularConnectingIsoOfQuasiIsoAt U' V' n hn)
    (connecting_naturality f hf U V U' V' hU hV n)

theorem singularConnectingIsoOfQuasiIsoAt_naturality_apply
    (f : X → Y) (hf : Continuous f) (U V : Set X) (U' V' : Set Y)
    [ContractibleSpace U] [ContractibleSpace V]
    [ContractibleSpace U'] [ContractibleSpace V']
    (hU : Set.MapsTo f U U') (hV : Set.MapsTo f V V') (n : ℕ) (hn : n ≠ 0)
    [QuasiIsoAt (inclusion (binaryCover U V)) (n + 1)]
    [QuasiIsoAt (inclusion (binaryCover U' V')) (n + 1)]
    (v : RealSingularHomology (n + 1) X) :
    (singularConnectingIsoOfQuasiIsoAt U' V' n hn).hom (realHomologyMap (n + 1) f hf v) =
      realHomologyMap n (intersectionMap f hf U V U' V' hU hV)
        (intersectionMap f hf U V U' V' hU hV).continuous
        ((singularConnectingIsoOfQuasiIsoAt U V n hn).hom v) := by
  exact congrArg (fun k : RealSingularHomology (n + 1) X ⟶
      RealSingularHomology n ↥(U' ∩ V') => k v)
    (singularConnectingIsoOfQuasiIsoAt_naturality f hf U V U' V' hU hV n hn)

end Problem340.SmallCoverMayerVietoris

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.CircleClockDoubling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.CircleClockDoubling

theorem clockDouble_eq_conjugateMap :
    clockDouble = conjugateMap homeomorph angularDouble := by
  funext x
  rw [conjugateMap, homeomorph_angularDouble, Homeomorph.apply_symm_apply]

theorem homologyEquiv_intertwines (n : ℕ) (v : RealSingularHomology n AngularCircle) :
    realHomologyMap n clockDouble continuous_clockDouble (homologyEquiv n v) =
      homologyEquiv n (realHomologyMap n angularDouble continuous_angularDouble v) := by
  simpa only [clockDouble_eq_conjugateMap, homologyEquiv] using
    realHomologyEquiv_conjugateMap n homeomorph continuous_angularDouble v

theorem eigenvector_transport (n : ℕ) (c : ℝ)
    (v : RealSingularHomology n AngularCircle) (hv : v ≠ 0)
    (heigen : realHomologyMap n angularDouble continuous_angularDouble v = c • v) :
    ∃ w : RealSingularHomology n StandardClock, w ≠ 0 ∧
      realHomologyMap n clockDouble continuous_clockDouble w = c • w := by
  refine ⟨homologyEquiv n v, ?_, ?_⟩
  · exact (map_ne_zero_iff (homologyEquiv n) (homologyEquiv n).injective).2 hv
  · rw [homologyEquiv_intertwines, heigen, map_smul]

end Problem340.CircleClockDoubling

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.CircleDoublingChains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

namespace Problem340.CircleDoublingChains

lemma triangle_face_zero : singularSet.δ 0 triangleSimplex = loopSimplex := by
  apply (TopCat.toSSetObjEquiv (TopCat.of Circle) _).injective
  ext p
  change SStd ℝ (Fin 2) at p
  change ((SStd.map (0 : Fin 3).succAbove p) 1 +
    2 * (SStd.map (0 : Fin 3).succAbove p) 2 : ℝ) = (p 1 : Circle)
  have h0 : (SStd.map (0 : Fin 3).succAbove p) 1 = p 0 := by
    have hf : (Finset.univ.filter fun x : Fin 2 =>
        (0 : Fin 3).succAbove x = (1 : Fin 3)) = {0} := by decide
    simp only [RealSimplex.map_apply, hf, Finset.sum_singleton]
  have h1 : (SStd.map (0 : Fin 3).succAbove p) 2 = p 1 := by
    have hf : (Finset.univ.filter fun x : Fin 2 =>
        (0 : Fin 3).succAbove x = (2 : Fin 3)) = {1} := by decide
    simp only [RealSimplex.map_apply, hf, Finset.sum_singleton]
  rw [h0, h1]
  have hsum : p 0 + p 1 = 1 := by
    simpa only [Fin.sum_univ_two] using p.total_of_fintype
  have hp : p 0 + 2 * p 1 = p 1 + 1 := by linarith
  rw [hp, AddCircle.coe_add_period]

lemma triangle_face_one : singularSet.δ 1 triangleSimplex = doubledLoopSimplex := by
  apply (TopCat.toSSetObjEquiv (TopCat.of Circle) _).injective
  ext p
  change SStd ℝ (Fin 2) at p
  change ((SStd.map (1 : Fin 3).succAbove p) 1 +
    2 * (SStd.map (1 : Fin 3).succAbove p) 2 : ℝ) = (p 1 : Circle) + (p 1 : Circle)
  have h0 : (SStd.map (1 : Fin 3).succAbove p) 1 = 0 := by
    have hf : (Finset.univ.filter fun x : Fin 2 =>
        (1 : Fin 3).succAbove x = (1 : Fin 3)) = ∅ := by decide
    simp only [RealSimplex.map_apply, hf, Finset.sum_empty]
  have h1 : (SStd.map (1 : Fin 3).succAbove p) 2 = p 1 := by
    have hf : (Finset.univ.filter fun x : Fin 2 =>
        (1 : Fin 3).succAbove x = (2 : Fin 3)) = {1} := by decide
    simp only [RealSimplex.map_apply, hf, Finset.sum_singleton]
  rw [h0, h1, zero_add, two_mul, AddCircle.coe_add]

lemma triangle_face_two : singularSet.δ 2 triangleSimplex = loopSimplex := by
  apply (TopCat.toSSetObjEquiv (TopCat.of Circle) _).injective
  ext p
  change SStd ℝ (Fin 2) at p
  change ((SStd.map (2 : Fin 3).succAbove p) 1 +
    2 * (SStd.map (2 : Fin 3).succAbove p) 2 : ℝ) = (p 1 : Circle)
  have h0 : (SStd.map (2 : Fin 3).succAbove p) 1 = p 1 := by
    have hf : (Finset.univ.filter fun x : Fin 2 =>
        (2 : Fin 3).succAbove x = (1 : Fin 3)) = {1} := by decide
    simp only [RealSimplex.map_apply, hf, Finset.sum_singleton]
  have h1 : (SStd.map (2 : Fin 3).succAbove p) 2 = 0 := by
    have hf : (Finset.univ.filter fun x : Fin 2 =>
        (2 : Fin 3).succAbove x = (2 : Fin 3)) = ∅ := by decide
    simp only [RealSimplex.map_apply, hf, Finset.sum_empty]
  rw [h0, h1, mul_zero, add_zero]

lemma triangleChain_boundary :
    triangleChain ≫ chains.d 2 1 = loopChain - doubledLoopChain + loopChain := by
  change singularSet.ιChainComplex triangleSimplex ≫
    (singularSet.chainComplex coefficients).d 2 1 = _
  rw [SSet.ιChainComplex_d]
  change (∑ i : Fin 3, (-1 : ℤ) ^ i.val • singularSet.ιChainComplex (singularSet.δ i triangleSimplex)) = _
  simp only [Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two,
    pow_zero, pow_one, neg_one_sq, one_smul, neg_smul,
    triangle_face_zero, triangle_face_one, triangle_face_two,
    loopChain, doubledLoopChain]
  erw [sub_eq_add_neg]
  rfl

lemma doubledLoopSimplex_eq_map : doubledLoopSimplex =
    (TopCat.toSSet.map (TopCat.ofHom doublingMap)).app _ loopSimplex := by
  rfl

lemma doubledLoopChain_eq_map :
    doubledLoopChain = loopChain ≫ (realSingularChainMap doubling continuous_doubling).f 1 := by
  rw [loopChain]
  change _ = singularSet.ιChainComplex loopSimplex ≫
    (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom doublingMap)) coefficients).f 1
  rw [SSet.ι_chainComplexMap_f]
  exact congrArg singularSet.ιChainComplex doubledLoopSimplex_eq_map

lemma triangle_boundary : (chains.d 2 1).hom triangle =
    loop - ((realSingularChainMap doubling continuous_doubling).f 1).hom loop + loop := by
  have h := ConcreteCategory.congr_hom triangleChain_boundary (1 : ℝ)
  rw [doubledLoopChain_eq_map] at h
  exact h

lemma doubling_loop_sub_two_is_boundary :
    ∃ w : chains.X 2, (chains.d 2 1).hom w =
      ((realSingularChainMap doubling continuous_doubling).f 1).hom loop - (2 : ℝ) • loop := by
  refine ⟨-triangle, ?_⟩
  rw [map_neg, triangle_boundary, two_smul]
  abel

lemma loopClass_eq_zero_iff : loopClass = 0 ↔
    ∃ w : chains.X 2, (chains.d 2 1).hom w = loop := by
  have h := moduleHomologyClass_eq_zero_iff (chains.sc 1)
    (show (chains.sc 1).X₂ from loop) loop_cycle_sc
  change loopClass = 0 ↔ (∃ w : chains.X ((ComplexShape.down ℕ).prev 1),
    (chains.d ((ComplexShape.down ℕ).prev 1) 1).hom w = loop) at h
  rw [ChainComplex.prev ℕ 1] at h
  exact h

theorem doubling_loopClass :
    realHomologyMap 1 doubling continuous_doubling loopClass = (2 : ℝ) • loopClass := by
  let S := chains.sc 1
  let z : S.X₂ := loop
  let φ : S ⟶ S :=
    (HomologicalComplex.shortComplexFunctor (ModuleCat ℝ) (ComplexShape.down ℕ) 1).map
      (realSingularChainMap doubling continuous_doubling)
  have hz : S.g.hom z = 0 := loop_cycle_sc
  have hz' : S.g.hom (φ.τ₂.hom z) = 0 := by
    have h := congrArg (fun k : S.X₂ ⟶ S.X₃ => k.hom z) φ.comm₂₃
    change S.g.hom (φ.τ₂.hom z) = φ.τ₃.hom (S.g.hom z) at h
    simpa only [hz, map_zero] using h
  have hdiff : S.g.hom (φ.τ₂.hom z - (2 : ℝ) • z) = 0 := by
    simp only [map_sub, map_smul, hz', hz, smul_zero, sub_self]
  have he : ∃ w : S.X₁, S.f.hom w = φ.τ₂.hom z - (2 : ℝ) • z := by
    change ∃ w : chains.X ((ComplexShape.down ℕ).prev 1),
      (chains.d ((ComplexShape.down ℕ).prev 1) 1).hom w =
        ((realSingularChainMap doubling continuous_doubling).f 1).hom loop - (2 : ℝ) • loop
    rw [ChainComplex.prev ℕ 1]
    exact doubling_loop_sub_two_is_boundary
  let π : LinearMap.ker S.g.hom →ₗ[ℝ] S.homology :=
    S.moduleCatHomologyIso.toLinearEquiv.symm.toLinearMap.comp
      (LinearMap.range S.moduleCatToCycles).mkQ
  let u : LinearMap.ker S.g.hom := ⟨z, LinearMap.mem_ker.mpr hz⟩
  let u' : LinearMap.ker S.g.hom := ⟨φ.τ₂.hom z, LinearMap.mem_ker.mpr hz'⟩
  have hzero := (moduleHomologyClass_eq_zero_iff S
    (φ.τ₂.hom z - (2 : ℝ) • z) hdiff).mpr he
  change π (u' - (2 : ℝ) • u) = 0 at hzero
  have heq : π u' = (2 : ℝ) • π u := by
    apply sub_eq_zero.mp
    simpa only [map_sub, map_smul] using hzero
  change (ShortComplex.homologyMap φ).hom (moduleHomologyClass S z hz) =
    (2 : ℝ) • moduleHomologyClass S z hz
  rw [moduleHomologyClass_map φ z hz hz']
  exact heq

end Problem340.CircleDoublingChains

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SingularSimplexCircleLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.SingularSimplexCircleLift

theorem sub_eq_sub_of_lifts {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    (F G : C(X, ℝ)) (h : ∀ x, (F x : Circle) = (G x : Circle)) (x y : X) :
    F x - F y = G x - G y := by
  have hc : ∀ z : X, ((F z - G z : ℝ) : Circle) = 0 := by
    intro z
    rw [AddCircle.coe_sub, h z, sub_self]
  have he := (AddCircle.isCoveringMap_coe (1 : ℝ)).const_of_comp
    (F.continuous.sub G.continuous) (fun a b => (hc a).trans (hc b).symm) x y
  change F x - G x = F y - G y at he
  linarith

theorem increment_eq {n : ℕ} (σ : C(Simplex n, Circle))
    (F : C(Simplex n, ℝ)) (hF : ∀ x, (F x : Circle) = σ x) (x y : Simplex n) :
    increment σ x y = F y - F x := by
  apply sub_eq_sub_of_lifts
  intro z
  exact (coe_lift σ z).trans (hF z).symm

theorem increment_comp {n m : ℕ} (σ : C(Simplex n, Circle))
    (φ : C(Simplex m, Simplex n)) (x y : Simplex m) :
    increment (σ.comp φ) x y = increment σ (φ x) (φ y) := by
  exact increment_eq (σ.comp φ) ((lift σ).comp φ)
    (fun z => coe_lift σ (φ z)) x y

theorem increment_map {n m : ℕ} (σ : C(Simplex n, Circle))
    (f : Fin (m + 1) → Fin (n + 1)) (x y : Simplex m) :
    increment (σ.comp ⟨SStd.map f, SStd.continuous_map ℝ f⟩) x y =
      increment σ (SStd.map f x) (SStd.map f y) :=
  increment_comp σ _ x y

theorem increment_map_vertices {n m : ℕ} (σ : C(Simplex n, Circle))
    (f : Fin (m + 1) → Fin (n + 1)) (i j : Fin (m + 1)) :
    increment (σ.comp ⟨SStd.map f, SStd.continuous_map ℝ f⟩)
      (SStd.single i) (SStd.single j) =
      increment σ (SStd.single (f i)) (SStd.single (f j)) := by
  rw [increment_map, SStd.map_single, SStd.map_single]

theorem increment_triangle (σ : C(Simplex 2, Circle)) :
    increment σ (SStd.single 1) (SStd.single 2) -
      increment σ (SStd.single 0) (SStd.single 2) +
      increment σ (SStd.single 0) (SStd.single 1) = 0 := by
  dsimp [increment]
  ring

end Problem340.SingularSimplexCircleLift

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.CircleWindingCocycle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

namespace Problem340.CircleWinding

theorem cochainOfIncrement_boundary (w : singularSet _⦋1⦌ → ℝ)
    (hw : ∀ σ : singularSet _⦋2⦌,
      w (singularSet.δ 0 σ) - w (singularSet.δ 1 σ) + w (singularSet.δ 2 σ) = 0) :
    chains.d 2 1 ≫ cochainOfIncrement w = 0 := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, SSet.ιChainComplex_d]
  simp [Fin.sum_univ_succ, Preadditive.add_comp]
  ext
  simpa [sub_eq_add_neg, add_assoc] using hw σ

lemma simplexIncrement_face (σ : singularSet _⦋2⦌) (i : Fin 3) :
    simplexIncrement (singularSet.δ i σ) =
      SingularSimplexCircleLift.increment ((TopCat.of CircleSpace).toSSetObjEquiv _ σ)
        (SStd.single (i.succAbove 0)) (SStd.single (i.succAbove 1)) := by
  change SingularSimplexCircleLift.increment
    (((TopCat.of CircleSpace).toSSetObjEquiv _ σ).comp
      ⟨SStd.map i.succAbove, SStd.continuous_map ℝ i.succAbove⟩)
    (SStd.single 0) (SStd.single 1) = _
  exact SingularSimplexCircleLift.increment_map_vertices _ _ _ _

lemma simplexIncrement_triangle (σ : singularSet _⦋2⦌) :
    simplexIncrement (singularSet.δ 0 σ) - simplexIncrement (singularSet.δ 1 σ) +
      simplexIncrement (singularSet.δ 2 σ) = 0 := by
  simp only [simplexIncrement_face]
  exact SingularSimplexCircleLift.increment_triangle _

theorem boundary_windingCochain : chains.d 2 1 ≫ windingCochain = 0 :=
  cochainOfIncrement_boundary simplexIncrement simplexIncrement_triangle

@[simp] theorem windingCochain_boundary (b : chains.X 2) :
    windingCochain.hom ((chains.d 2 1).hom b) = 0 := by
  exact congrArg (fun f : chains.X 2 ⟶ coefficients => f.hom b) boundary_windingCochain

theorem simplexIncrement_loop :
    simplexIncrement CircleDoublingChains.loopSimplex = 1 := by
  change SingularSimplexCircleLift.increment CircleDoublingChains.loopMap
    (SStd.single 0) (SStd.single 1) = 1
  let F : C(SStd ℝ (Fin 2), ℝ) :=
    ⟨fun p => p 1, SStd.continuous_weights_apply ℝ 1⟩
  rw [SingularSimplexCircleLift.increment_eq _ F (fun _ => rfl)]
  norm_num [F]

theorem windingCochain_loop : windingCochain.hom CircleDoublingChains.loop = 1 := by
  change (singularSet.ιChainComplex CircleDoublingChains.loopSimplex ≫
    cochainOfIncrement simplexIncrement).hom (1 : ℝ) = 1
  rw [generator_cochainOfIncrement]
  change (1 : ℝ) • simplexIncrement CircleDoublingChains.loopSimplex = 1
  rw [one_smul, simplexIncrement_loop]

theorem loop_not_boundary :
    ¬ ∃ b : CircleDoublingChains.chains.X 2,
      (CircleDoublingChains.chains.d 2 1).hom b = CircleDoublingChains.loop := by
  rintro ⟨b, hb⟩
  have h := windingCochain_boundary b
  change windingCochain.hom ((CircleDoublingChains.chains.d 2 1).hom b) = 0 at h
  rw [hb, windingCochain_loop] at h
  norm_num at h

end Problem340.CircleWinding

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.CircleHomologySupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.CircleHomology

theorem loopClass_ne_zero : CircleDoublingChains.loopClass ≠ 0 :=
  mt CircleDoublingChains.loopClass_eq_zero_iff.mp CircleWinding.loop_not_boundary

theorem exists_clock_doubling_eigenvector :
    ∃ v : RealSingularHomology 1 StandardClock, v ≠ 0 ∧
      realHomologyMap 1 CircleClockDoubling.clockDouble
        CircleClockDoubling.continuous_clockDouble v = (2 : ℝ) • v :=
  CircleClockDoubling.eigenvector_transport 1 2 CircleDoublingChains.loopClass
    loopClass_ne_zero CircleDoublingChains.doubling_loopClass

end Problem340.CircleHomology

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SphereCoverGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Problem340.SphereCover

lemma south_ne_north : chartSouthPole ≠ chartNorthPole :=
  sphereOfComplex_ne_north 0

lemma isOpen_northComplement : IsOpen northComplement := isOpen_compl_singleton

lemma isOpen_southComplement : IsOpen southComplement := isOpen_compl_singleton

lemma cover : northComplement ∪ southComplement = Set.univ := by
  ext x
  simp only [northComplement, southComplement, Set.mem_union, Set.mem_compl_iff,
    Set.mem_singleton_iff, Set.mem_univ, iff_true]
  by_cases h : x = chartNorthPole
  · exact Or.inr (by simpa [h] using south_ne_north.symm)
  · exact Or.inl h

end Problem340.SphereCover

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SphereOverlapDoubling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.SphereOverlapDoubling

open SphereCover

lemma radialRetraction_square (z : PuncturedPlane) :
    radialRetraction (puncturedSquare z) = radialRetraction z ^ 2 := by
  apply Subtype.ext
  change ‖z.val ^ 2‖⁻¹ • z.val ^ 2 = (‖z.val‖⁻¹ • z.val) ^ 2
  rw [norm_pow, ← inv_pow, smul_pow]

lemma overlapSquare_coe (x : Overlap) :
    (overlapSquare x).val = SphereDoubling.sphereMap x.val := by
  change sphereOfComplex (sphereToComplex x.val ^ 2) = SphereDoubling.sphereMap x.val
  rw [← sphereDoubling_sphereOfComplex, sphereOfComplex_sphereToComplex x.property.1]

lemma overlapHomeomorph_square (x : Overlap) :
    overlapHomeomorph (overlapSquare x) = puncturedSquare (overlapHomeomorph x) :=
  overlapHomeomorph.apply_symm_apply _

lemma circleHomeomorphClock_eq : circleHomeomorphClock = circleClockHomeomorph := by
  ext z
  rfl

lemma overlapEquivClock_square (x : Overlap) :
    overlapEquivClock (overlapSquare x) =
      CircleClockDoubling.clockDouble (overlapEquivClock x) := by
  change circleHomeomorphClock (radialRetraction (overlapHomeomorph (overlapSquare x))) =
    CircleClockDoubling.clockDouble
      (circleHomeomorphClock (radialRetraction (overlapHomeomorph x)))
  rw [overlapHomeomorph_square, radialRetraction_square, circleHomeomorphClock_eq]
  change circleClockHomeomorph ((radialRetraction (overlapHomeomorph x) : Circle) ^ 2) =
    circleClockHomeomorph ((circleClockHomeomorph.symm
      (circleClockHomeomorph (radialRetraction (overlapHomeomorph x)))) ^ 2)
  exact congrArg circleClockHomeomorph
    (congrArg (fun z : Circle => z ^ 2)
      (circleClockHomeomorph.symm_apply_apply (radialRetraction (overlapHomeomorph x)))).symm

lemma overlapHomologyEquivClock_intertwines (n : ℕ)
    (v : RealSingularHomology n Overlap) :
    overlapHomologyEquivClock n
        (realHomologyMap n overlapSquare continuous_overlapSquare v) =
      realHomologyMap n CircleClockDoubling.clockDouble
        CircleClockDoubling.continuous_clockDouble (overlapHomologyEquivClock n v) := by
  change realHomologyMap n overlapEquivClock overlapEquivClock.continuous
      (realHomologyMap n overlapSquare continuous_overlapSquare v) =
    realHomologyMap n CircleClockDoubling.clockDouble
      CircleClockDoubling.continuous_clockDouble
      (realHomologyMap n overlapEquivClock overlapEquivClock.continuous v)
  have hcomp : (overlapEquivClock : Overlap → StandardClock) ∘ overlapSquare =
      CircleClockDoubling.clockDouble ∘ overlapEquivClock :=
    funext overlapEquivClock_square
  have hmap := congrArg (fun A => A v)
    (realHomologyMap_comp n overlapSquare overlapEquivClock continuous_overlapSquare
      overlapEquivClock.continuous).symm
  change realHomologyMap n overlapEquivClock overlapEquivClock.continuous
      (realHomologyMap n overlapSquare continuous_overlapSquare v) =
    realHomologyMap n (overlapEquivClock ∘ overlapSquare)
      (overlapEquivClock.continuous.comp continuous_overlapSquare) v at hmap
  have heq : realHomologyMap n (overlapEquivClock ∘ overlapSquare)
      (overlapEquivClock.continuous.comp continuous_overlapSquare) =
      realHomologyMap n (CircleClockDoubling.clockDouble ∘ overlapEquivClock)
        (CircleClockDoubling.continuous_clockDouble.comp overlapEquivClock.continuous) := by
    congr 1
  rw [hmap, heq, realHomologyMap_comp]
  rfl

end Problem340.SphereOverlapDoubling

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SphereMayerVietorisEigen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory

namespace Problem340.SphereMayerVietorisEigen

open SphereCover SingularSmallChains SmallCoverMayerVietoris

lemma restrictMap_eq_overlapSquare :
    (restrictMap SphereDoubling.sphereMap SphereDoubling.continuous_sphereMap
      (northComplement ∩ southComplement) (northComplement ∩ southComplement)
      (fun _ hx => ⟨mapsTo_northComplement hx.1, mapsTo_southComplement hx.2⟩) :
        SphereOverlapDoubling.Overlap → SphereOverlapDoubling.Overlap) =
      SphereOverlapDoubling.overlapSquare := by
  funext x
  apply Subtype.ext
  exact (SphereOverlapDoubling.overlapSquare_coe x).symm

lemma coverFamily_isOpen (b : Bool) : IsOpen (coverFamily b) := by
  cases b
  · exact isOpen_southComplement
  · exact isOpen_northComplement

lemma coverFamily_covers (x : StandardSphere2) : ∃ b, x ∈ coverFamily b := by
  have hx : x ∈ northComplement ∪ southComplement := by
    rw [SphereCover.cover]
    trivial
  rcases hx with hx | hx
  · exact ⟨true, hx⟩
  · exact ⟨false, hx⟩

lemma iUnion_coverFamily : (⋃ b, coverFamily b) = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact coverFamily_covers x

theorem exists_overlap_square_eigenvector :
    ∃ v : RealSingularHomology 1 SphereOverlapDoubling.Overlap, v ≠ 0 ∧
      realHomologyMap 1 SphereOverlapDoubling.overlapSquare
        SphereOverlapDoubling.continuous_overlapSquare v = (2 : ℝ) • v := by
  obtain ⟨w, hw, heigen⟩ := CircleHomology.exists_clock_doubling_eigenvector
  let e := overlapHomologyEquivClock 1
  refine ⟨e.symm w, ?_, ?_⟩
  · exact (map_ne_zero_iff e.symm e.symm.injective).2 hw
  · apply e.injective
    change overlapHomologyEquivClock 1
      (realHomologyMap 1 SphereOverlapDoubling.overlapSquare
        SphereOverlapDoubling.continuous_overlapSquare (e.symm w)) =
      e ((2 : ℝ) • e.symm w)
    rw [SphereOverlapDoubling.overlapHomologyEquivClock_intertwines]
    change realHomologyMap 1 CircleClockDoubling.clockDouble
      CircleClockDoubling.continuous_clockDouble (e (e.symm w)) =
      e ((2 : ℝ) • e.symm w)
    rw [e.apply_symm_apply, heigen, map_smul, e.apply_symm_apply]

end Problem340.SphereMayerVietorisEigen

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SphereSquareHomologyTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340

theorem rawSphereSquare_eq_conjugate_standard :
    rawSphereSquare = conjugateMap complexSphereHomeomorph.symm SphereDoubling.sphereMap := by
  funext z
  apply complexSphereHomeomorph.injective
  simpa only [conjugateMap, Homeomorph.symm_symm, Homeomorph.apply_symm_apply,
    rawSphereSquare] using (sphereDoubling_complexSphereHomeomorph z).symm

theorem rawSphereSquare_eigenvector_of_standard (n : ℕ) (c : ℝ)
    (v : RealSingularHomology n StandardSphere2) (hv : v ≠ 0)
    (heig : realHomologyMap n SphereDoubling.sphereMap
      SphereDoubling.continuous_sphereMap v = c • v) :
    ∃ w : RealSingularHomology n (OnePoint ℂ), w ≠ 0 ∧
      realHomologyMap n rawSphereSquare continuous_rawSphereSquare w = c • w := by
  obtain ⟨w, hw, he⟩ := realHomologyMap_eigenvector_conjugateMap n
    complexSphereHomeomorph.symm SphereDoubling.continuous_sphereMap c v hv heig
  exact ⟨w, hw, by simpa only [← rawSphereSquare_eq_conjugate_standard] using he⟩

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.Assembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
open Problem340 Problem340.SphereCover Problem340.SingularSmallChains
open Problem340.SmallCoverMayerVietoris Problem340.SphereMayerVietorisEigen
namespace Problem340.CounterexampleAssembly804

theorem sphereEigen : ∃ v : RealSingularHomology 2 StandardSphere2, v ≠ 0 ∧
    realHomologyMap 2 SphereDoubling.sphereMap SphereDoubling.continuous_sphereMap v =
      (2 : ℝ) • v := by
  let : QuasiIso (inclusion coverFamily) :=
    inclusion_quasiIso_of_natural_subdivision_zero coverFamily
      ActualSingularSubdivision.chainMap ActualSingularSubdivision.chainMap_app_zero
      (exists_actualSubdivision_pow_mem_range coverFamily coverFamily_isOpen
        (by rw [iUnion_coverFamily]))
  let e := (singularConnectingIsoOfQuasiIsoAt northComplement southComplement 1
    (by decide)).toLinearEquiv
  obtain ⟨w, hw, heigen⟩ := exists_overlap_square_eigenvector
  refine ⟨e.symm w, (map_ne_zero_iff e.symm e.symm.injective).2 hw, ?_⟩
  apply e.injective
  have h := singularConnectingIsoOfQuasiIsoAt_naturality_apply
    SphereDoubling.sphereMap SphereDoubling.continuous_sphereMap
    northComplement southComplement northComplement southComplement
    mapsTo_northComplement mapsTo_southComplement 1 (by decide) (e.symm w)
  have hh : e (realHomologyMap 2 SphereDoubling.sphereMap
      SphereDoubling.continuous_sphereMap (e.symm w)) =
      realHomologyMap 1 SphereOverlapDoubling.overlapSquare
        SphereOverlapDoubling.continuous_overlapSquare (e (e.symm w)) := by
    simpa only [e, CategoryTheory.Iso.toLinearEquiv_apply, intersectionMap, restrictMap_eq_overlapSquare] using h
  rw [hh, e.apply_symm_apply, heigen, map_smul, e.apply_symm_apply]

theorem exists_counterexample :
    ∃ q : ℕ, 0 < q ∧ ∃ f : CounterexampleManifold q → CounterexampleManifold q, ∃ hf : IsC1SelfMap q f, Dynamics.coverEntropy f (Set.univ : Set (CounterexampleManifold q)) = (0 : EReal) ∧ (∃ v : RealSingularHomology 2 (CounterexampleManifold q), v ≠ 0 ∧ realHomologyMap 2 f hf.1 v = (2 : ℝ) • v) ∧ 0 < Real.log (2 : ℝ) ∧ Real.log (2 : ℝ) ≤ Real.log (totalRealHomologySpectralRadius f hf.1) ∧ ¬ Function.Bijective f ∧ 5 ≤ 2 * q + 3 := by
  have hsphere : ∃ v : RealSingularHomology 2 (OnePoint ℂ), v ≠ 0 ∧
      realHomologyMap 2 rawSphereSquare continuous_rawSphereSquare v = (2 : ℝ) • v := by
    obtain ⟨v, hv, he⟩ := sphereEigen
    exact rawSphereSquare_eigenvector_of_standard 2 2 v hv he
  let G := CoordinateGoodCover.rawBaseGoodCover
  let : QuasiIso (inclusion G.carrier) :=
    inclusion_quasiIso_of_natural_subdivision_zero G.carrier
      ActualSingularSubdivision.chainMap ActualSingularSubdivision.chainMap_app_zero
      (exists_actualSubdivision_pow_mem_range G.carrier G.isOpen
        (by rw [G.iUnion_eq_univ]))
  exact Construction.exists_counterexample_of_sphere_and_base_homology hsphere
    FiniteCoverHomology.rawBase_homologyEigenvalueRadii_bddAbove

end Problem340.CounterexampleAssembly804

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.Counterexample
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340

theorem exists_C1_entropy_counterexample_oai :
    ∃ q : ℕ, 0 < q ∧ ∃ f : CounterexampleManifold q → CounterexampleManifold q, ∃ hf : IsC1SelfMap q f, Dynamics.coverEntropy f (Set.univ : Set (CounterexampleManifold q)) = (0 : EReal) ∧ (∃ v : RealSingularHomology 2 (CounterexampleManifold q), v ≠ 0 ∧ realHomologyMap 2 f hf.1 v = (2 : ℝ) • v) ∧ 0 < Real.log (2 : ℝ) ∧ Real.log (2 : ℝ) ≤ Real.log (totalRealHomologySpectralRadius f hf.1) ∧ ¬ Function.Bijective f ∧ 5 ≤ 2 * q + 3 := by
  exact CounterexampleAssembly804.exists_counterexample

end Problem340

end

end OAI
end

theorem solution : type_of% @OAI.Problem340.exists_C1_entropy_counterexample_oai := @OAI.Problem340.exists_C1_entropy_counterexample_oai
