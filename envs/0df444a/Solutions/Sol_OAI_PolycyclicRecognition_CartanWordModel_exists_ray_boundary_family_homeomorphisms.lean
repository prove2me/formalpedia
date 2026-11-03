-- Prove2me | solution 1 for OAI.PolycyclicRecognition.CartanWordModel.exists_ray_boundary_family_homeomorphisms
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-03T00:52:02.226133+00:00
-- url     : https://prove2.me/submissions/e6f9d995-b60c-4a7a-9f6c-18c0fc3f0a3b

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D022
import Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_RayBoundaryModel_contracts_compact_orbits_m
import Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_continuous_bounded_ray_quotient_limits
import Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_exists_boundary_family_with_compact_shadow

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CompactLiftQuotient
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact lifts and the topology of the actual quotient orbit -/

noncomputable section
namespace PolycyclicRecognition

open Set TopologicalSpace Topology
open scoped Manifold

/-- A continuous surjection with compact lifts of compact sets is a
quotient map into a Hausdorff compactly generated space. -/
theorem isQuotientMap_of_compact_lifts
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space Y] [CompactlyGeneratedSpace Y]
    (f : X → Y) (hf : Continuous f) (hsurj : Function.Surjective f)
    (hlift : ∀ K : Set Y, IsCompact K → ∃ C : Set X, IsCompact C ∧ K ⊆ f '' C) :
    IsQuotientMap f := by
  refine isQuotientMap_iff_isClosed.mpr ⟨hsurj, fun S => ⟨fun h => h.preimage hf, ?_⟩⟩
  intro hS
  apply (CompactlyGeneratedSpace.isClosed_iff_of_t2 S).mpr
  intro K hK
  obtain ⟨C, hC, hcover⟩ := hlift K hK
  have hc : IsCompact ((C ∩ f ⁻¹' S) ∩ f ⁻¹' K) :=
    (hC.inter_right hS).inter_right (hK.isClosed.preimage hf)
  have he : f '' ((C ∩ f ⁻¹' S) ∩ f ⁻¹' K) = S ∩ K := by
    ext y
    constructor
    · rintro ⟨x, ⟨⟨_, hxS⟩, hxK⟩, rfl⟩
      exact ⟨hxS, hxK⟩
    · rintro ⟨hyS, hyK⟩
      obtain ⟨x, hxC, hxy⟩ := hcover hyK
      exact ⟨x, ⟨⟨hxC, by simpa only [mem_preimage, hxy] using hyS⟩,
        by simpa only [mem_preimage, hxy] using hyK⟩, hxy⟩
  rw [← he]
  exact (hc.image hf).isClosed

namespace CartanFactorModel

variable {EG G Q : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [TopologicalSpace Q] [Group Q]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

/-- The actual orbit map is a quotient map. Its topology follows from
compact Cartan lifts and a continuous section of the nilpotent projection. -/
theorem orbitMap_isQuotientMap
    (π : F.N.carrier →* Q) (hπ : Continuous π)
    (s : Q → F.N.carrier) (hs : Continuous s) (hsection : Function.RightInverse s π)
    (α : F.D.carrier →* MulAut Q) (act : G →* Equiv.Perm Q)
    (hact : ∀ u d q, act (F.inclusionN u * F.inclusionD d) q = π u * α d q) :
    IsQuotientMap (fun g => act g 1) := by
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  let p : F.N.carrier × F.D.carrier → G := fun z => F.inclusionN z.1 * F.inclusionD z.2
  have hp : IsQuotientMap p := isQuotientMap_of_compact_lifts p
    ((F.closedN.continuous.comp continuous_fst).mul (F.closedD.continuous.comp continuous_snd))
    F.surjective F.compactLifts
  have hcont : Continuous (fun g => act g 1) := hp.continuous_iff.mpr (by
    have hh : (fun z : F.N.carrier × F.D.carrier => act (p z) 1) =
        fun z => π z.1 := by
      funext z
      simp only [p, hact, map_one, mul_one]
    change Continuous (fun z => act (p z) 1)
    rw [hh]
    exact hπ.comp continuous_fst)
  have hright : Function.LeftInverse (fun g => act g 1) (fun q => F.inclusionN (s q)) := by
    intro q
    have hh := hact (s q) 1 1
    simpa only [map_one, mul_one, hsection q] using hh
  exact IsQuotientMap.of_inverse (F.closedN.continuous.comp hs) hcont hright

end CartanFactorModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_BoundaryInverseShadow
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transporting two compact shadows through a coarse inverse -/

noncomputable section
namespace PolycyclicRecognition

open Set Metric Filter
open scoped Pointwise Topology

/-- A continuous section turns a compact quotient shadow into compact
ambient representatives of that same shadow. -/
theorem compact_lift_boundary_shadow
    {G S T : Type} [Group G] [TopologicalSpace G]
    [One S] [One T] [TopologicalSpace T]
    (actS : G →* Equiv.Perm S) (actT : G →* Equiv.Perm T)
    (B : S → T) (f : G → G)
    (σ : T → G) (hσ : Continuous σ) (hsection : ∀ q, actT (σ q) 1 = q)
    (K : Set T) (hK : IsCompact K)
    (hshadow : ∀ x, ∃ q ∈ K, B (actS x 1) = actT (f x) q) :
    ∃ C : Set G, IsCompact C ∧ ∀ x, ∃ u ∈ C,
      B (actS x 1) = actT (f x) (actT u 1) := by
  refine ⟨σ '' K, hK.image hσ, ?_⟩
  intro x
  obtain ⟨q, hq, he⟩ := hshadow x
  exact ⟨σ q, ⟨q, hq, rfl⟩, by simpa only [hsection] using he⟩

/-- Compose the forward and inverse boundary shadows. Compact group
representatives of the shadows and the coarse-inverse estimate put their
composition in one fixed compact source shadow. -/
theorem inverse_boundary_compact_shadow
    {G S T : Type} [Group G] [MetricSpace G] [IsTopologicalGroup G]
    [IsIsometricSMul G G] [ProperSpace G] [One S] [One T]
    (actS : G →* Equiv.Perm S) (actT : G →* Equiv.Perm T)
    (B : S → T) (C : T → S) (f g : G → G)
    {L error E : ℝ} (hL : 0 ≤ L)
    (hg : ∀ x y, dist (g x) (g y) ≤ L * dist x y + error)
    (hinv : ∀ x, dist (g (f x)) x ≤ E)
    (KT KS : Set G) (hKT : IsCompact KT) (hKS : IsCompact KS)
    (hB : ∀ x, ∃ u ∈ KT, B (actS x 1) = actT (f x) (actT u 1))
    (hC : ∀ y, ∃ v ∈ KS, C (actT y 1) = actS (g y) (actS v 1)) :
    ∃ K : Set G, IsCompact K ∧ ∀ x, ∃ k ∈ K,
      C (B (actS x 1)) = actS x (actS k 1) := by
  obtain ⟨R, hR⟩ := hKT.exists_bound_of_continuousOn
    ((continuous_const : Continuous (fun _ : G => (1 : G))).dist continuous_id).continuousOn
  have hR' (u : G) (hu : u ∈ KT) : dist 1 u ≤ R := by
    simpa only [id_eq, Real.norm_eq_abs, abs_of_nonneg dist_nonneg] using hR u hu
  let D := E + L * R + error
  refine ⟨closedBall (1 : G) D * KS, (isCompact_closedBall _ _).mul hKS, ?_⟩
  intro x
  obtain ⟨u, hu, hBu⟩ := hB x
  obtain ⟨v, hv, hCv⟩ := hC (f x * u)
  let δ := x⁻¹ * g (f x * u)
  have hδ : δ ∈ closedBall (1 : G) D := by
    have hdist : dist 1 δ = dist x (g (f x * u)) := by
      simpa only [δ, mul_one, mul_inv_cancel_left] using
        (dist_mul_left x (1 : G) (x⁻¹ * g (f x * u))).symm
    have hu' : dist (f x) (f x * u) = dist 1 u := by
      simpa only [mul_one] using dist_mul_left (f x) (1 : G) u
    have hcoarse := hg (f x) (f x * u)
    rw [hu'] at hcoarse
    have hmul := mul_le_mul_of_nonneg_left (hR' u hu) hL
    have hi := hinv x
    have ht := dist_triangle x (g (f x)) (g (f x * u))
    rw [dist_comm x (g (f x))] at ht
    rw [mem_closedBall, dist_comm, hdist]
    change dist x (g (f x * u)) ≤ E + L * R + error
    linarith
  refine ⟨δ * v, Set.mul_mem_mul hδ hv, ?_⟩
  have hpoint : actT (f x) (actT u 1) = actT (f x * u) 1 := by
    rw [map_mul, Equiv.Perm.mul_apply]
  have hgroup : x * (δ * v) = g (f x * u) * v := by
    simp only [δ, ← mul_assoc, mul_inv_cancel, one_mul]
  calc
    C (B (actS x 1)) = C (actT (f x * u) 1) := congrArg C (hBu.trans hpoint)
    _ = actS (g (f x * u)) (actS v 1) := hCv
    _ = actS (g (f x * u) * v) 1 := by rw [map_mul, Equiv.Perm.mul_apply]
    _ = actS (x * (δ * v)) 1 := by rw [hgroup]
    _ = actS x (actS (δ * v) 1) := by rw [map_mul, Equiv.Perm.mul_apply]

/-- A composition constrained by one compact source shadow is the
identity when the negative ray fixes the basepoint and contracts compact
shadows. The compact-shadow premise is supplied by the coarse-inverse
transport theorem above. -/
theorem boundary_left_inverse_of_compact_shadow
    {G S T : Type} [Group G] [TopologicalSpace G]
    [One S] [TopologicalSpace S] [T2Space S]
    (act : G →* Equiv.Perm S) (hact : ∀ g, Continuous (act g))
    (B : S → T) (C : T → S) (ray : ℕ → G)
    (hfix : ∀ n, act (ray n) 1 = 1)
    (hcontract : ∀ K : Set G, IsCompact K → ∀ k : ℕ → G,
      (∀ n, k n ∈ K) → Tendsto (fun n => act (ray n) (act (k n) 1)) atTop (𝓝 1))
    (hshadow : ∃ K : Set G, IsCompact K ∧ ∀ x, ∃ k ∈ K,
      C (B (act x 1)) = act x (act k 1)) :
    ∀ x, C (B (act x 1)) = act x 1 := by
  classical
  obtain ⟨K, hK, hshadow⟩ := hshadow
  intro x
  have hs (n : ℕ) : ∃ k ∈ K,
      C (B (act x 1)) = act x (act (ray n) (act k 1)) := by
    obtain ⟨k, hk, he⟩ := hshadow (x * ray n)
    refine ⟨k, hk, ?_⟩
    simpa only [map_mul, Equiv.Perm.mul_apply, hfix] using he
  choose k hk he using hs
  have ht := ((hact x).tendsto 1).comp (hcontract K hK k hk)
  have hconst : Tendsto (fun _ : ℕ => C (B (act x 1))) atTop (𝓝 (act x 1)) := by
    simpa only [Function.comp_def, ← he] using ht
  exact tendsto_nhds_unique tendsto_const_nhds hconst

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_BoundaryFamilyHomeomorphism
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Boundary homeomorphisms from coarse inverse compact shadows -/

noncomputable section
namespace PolycyclicRecognition

open Set Filter
open scoped Topology

/-- Contracting rays turn the two compact shadows of a coarse inverse pair
into inverse boundary maps. This applies to all members of a family with
the same compact shadow sets. -/
theorem boundary_family_homeomorphisms_of_compact_shadows
    {P G S T : Type} [Group G] [MetricSpace G] [IsTopologicalGroup G]
    [IsIsometricSMul G G] [ProperSpace G]
    [One S] [TopologicalSpace S] [T2Space S]
    [One T] [TopologicalSpace T] [T2Space T]
    (actS : G →* Equiv.Perm S) (actT : G →* Equiv.Perm T)
    (hcontS : ∀ g, Continuous (actS g)) (hcontT : ∀ g, Continuous (actT g))
    (σS : S → G) (hσS : Continuous σS) (hsectionS : ∀ q, actS (σS q) 1 = q)
    (σT : T → G) (hσT : Continuous σT) (hsectionT : ∀ q, actT (σT q) 1 = q)
    (rayS rayT : ℕ → G)
    (hfixS : ∀ n, actS (rayS n) 1 = 1) (hfixT : ∀ n, actT (rayT n) 1 = 1)
    (hcontractS : ∀ K : Set G, IsCompact K → ∀ k : ℕ → G,
      (∀ n, k n ∈ K) → Tendsto (fun n => actS (rayS n) (actS (k n) 1)) atTop (𝓝 1))
    (hcontractT : ∀ K : Set G, IsCompact K → ∀ k : ℕ → G,
      (∀ n, k n ∈ K) → Tendsto (fun n => actT (rayT n) (actT (k n) 1)) atTop (𝓝 1))
    (B : P → S → T) (C : P → T → S)
    (hBcont : ∀ p, Continuous (B p)) (hCcont : ∀ p, Continuous (C p))
    (f g : P → G → G) {Lf Lg ef eg E : ℝ} (hLf : 0 ≤ Lf) (hLg : 0 ≤ Lg)
    (hf : ∀ p x y, dist (f p x) (f p y) ≤ Lf * dist x y + ef)
    (hg : ∀ p x y, dist (g p x) (g p y) ≤ Lg * dist x y + eg)
    (hgf : ∀ p x, dist (g p (f p x)) x ≤ E)
    (hfg : ∀ p x, dist (f p (g p x)) x ≤ E)
    (KS : Set S) (KT : Set T) (hKS : IsCompact KS) (hKT : IsCompact KT)
    (hB : ∀ p x, ∃ q ∈ KT, B p (actS x 1) = actT (f p x) q)
    (hC : ∀ p x, ∃ q ∈ KS, C p (actT x 1) = actS (g p x) q) :
    ∃ D : P → S ≃ₜ T, (∀ p q, D p q = B p q) ∧
      (∀ p q, (D p).symm q = C p q) := by
  classical
  have hleft (p : P) : Function.LeftInverse (C p) (B p) := by
    obtain ⟨KT', hKT', hB'⟩ := compact_lift_boundary_shadow actS actT (B p) (f p)
      σT hσT hsectionT KT hKT (hB p)
    obtain ⟨KS', hKS', hC'⟩ := compact_lift_boundary_shadow actT actS (C p) (g p)
      σS hσS hsectionS KS hKS (hC p)
    have hshadow := inverse_boundary_compact_shadow actS actT (B p) (C p)
      (f p) (g p) hLg (hg p) (hgf p) KT' KS' hKT' hKS' hB' hC'
    have h := boundary_left_inverse_of_compact_shadow actS hcontS (B p) (C p)
      rayS hfixS hcontractS hshadow
    intro q
    simpa only [hsectionS] using h (σS q)
  have hright (p : P) : Function.RightInverse (C p) (B p) := by
    obtain ⟨KS', hKS', hC'⟩ := compact_lift_boundary_shadow actT actS (C p) (g p)
      σS hσS hsectionS KS hKS (hC p)
    obtain ⟨KT', hKT', hB'⟩ := compact_lift_boundary_shadow actS actT (B p) (f p)
      σT hσT hsectionT KT hKT (hB p)
    have hshadow := inverse_boundary_compact_shadow actT actS (C p) (B p)
      (g p) (f p) hLf (hf p) (hfg p) KS' KT' hKS' hKT' hC' hB'
    have h := boundary_left_inverse_of_compact_shadow actT hcontT (C p) (B p)
      rayT hfixT hcontractT hshadow
    intro q
    simpa only [hsectionT] using h (σT q)
  exact ⟨fun p => {
    toFun := B p, invFun := C p, left_inv := hleft p, right_inv := hright p
    continuous_toFun := hBcont p, continuous_invFun := hCcont p },
    fun _ _ => rfl, fun _ _ => rfl⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_BoundedCenteredHeight
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform height control on families with bounded centers -/

noncomputable section
namespace PolycyclicRecognition

/-- On a family with bounded image centers, a uniform centered height
estimate gives an uncentered estimate with one common additive constant. -/
theorem bounded_family_height_of_centered_uniform
    {G W P : Type} [Group G] [MetricSpace G]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (π : G →* Multiplicative W) (A : W →L[ℝ] W) (f : G → G)
    {K : ℝ} (hK : 0 ≤ K)
    (hLip : ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ K * dist x y)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ x g,
      ‖(π ((f x)⁻¹ * f (x * g))).toAdd - A ((π g).toAdd)‖ ≤ ε * dist 1 g + B)
    (center : P → G) {start : ℝ} (hstart : ∀ p, dist 1 (f (center p)) ≤ start) :
    ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ p g,
      ‖(π (f (center p * g))).toAdd - A ((π g).toAdd)‖ ≤ ε * dist 1 g + B := by
  intro ε hε
  obtain ⟨B, hB, hb⟩ := hsub ε hε
  refine ⟨B + K * |start|, by positivity, ?_⟩
  intro p g
  have hcenter : ‖(π (f (center p))).toAdd‖ ≤ K * |start| := by
    have hh := hLip (f (center p)) 1
    simp only [map_one, toAdd_one, sub_zero] at hh
    have hd : dist (f (center p)) 1 ≤ |start| := by
      simpa only [dist_comm] using (hstart p).trans (le_abs_self start)
    exact hh.trans (mul_le_mul_of_nonneg_left hd hK)
  have he : (π (f (center p * g))).toAdd - A ((π g).toAdd) =
      ((π ((f (center p))⁻¹ * f (center p * g))).toAdd - A ((π g).toAdd)) +
        (π (f (center p))).toAdd := by
    simp only [map_mul, map_inv, toAdd_mul, toAdd_inv]
    abel
  rw [he]
  exact (norm_add_le _ _).trans (by linarith [hb (center p) g])

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanWordBasis
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A homogeneous bracket-word basis of the Cartan ideal

This supplies actual nonzero-root letters and strictly positive integral
letter multiplicities for the nilpotent box data.
-/

noncomputable section

namespace PolycyclicRecognition

open LieAlgebra LieModule Module
open scoped BigOperators

variable {L : Type} [LieRing L] [LieAlgebra ℝ L]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

set_option maxHeartbeats 1000000 in
theorem cartanGeneratorPool_lieSpan [FiniteDimensional ℝ L]
    {n : ℕ} (T : TriangularAdjoint L n) :
    LieSubalgebra.lieSpan ℝ (cartanRootIdeal H) (cartanGeneratorPool H) = ⊤ := by
  let N := cartanRootIdeal H
  let U := LieSubalgebra.lieSpan ℝ N (cartanGeneratorPool H)
  have himage : N.incl '' cartanGeneratorPool H =
      {v | ∃ χ : Weight ℝ H L, χ.IsNonZero ∧ v ∈ rootSpace H χ} := by
    ext v
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hv
      have hN : v ∈ N := LieSubmodule.subset_lieSpan hv
      exact ⟨⟨v, hN⟩, hv, rfl⟩
  have hmap : U.map N.incl = N.toLieSubalgebra := by
    rw [LieSubalgebra.map_lieSpan, himage]
    change cartanRootSubalgebra H = N.toLieSubalgebra
    apply SetLike.coe_injective
    exact congrArg (fun V : Submodule ℝ L => (V : Set L))
      (cartanRootSubalgebra_eq_ideal H T)
  apply top_unique
  intro v _
  have hv : (v : L) ∈ U.map N.incl := by rw [hmap]; exact v.property
  obtain ⟨w, hw, heq⟩ := hv
  have : w = v := Subtype.ext heq
  change v ∈ U
  exact this ▸ hw

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanResidualAction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial bounds for the residual Cartan action

On an actual generalized root space, subtracting its scalar character leaves
an operator nilpotent in a uniform dimension bound. Its exponential therefore
has polynomial growth in the Cartan parameter. This supplies the residual
operator estimate used in box conjugation.
-/

noncomputable section

namespace PolycyclicRecognition

open LieAlgebra LieModule Module

set_option maxHeartbeats 1000000 in
/-- Split an arbitrary scalar character from an operator exponential. -/
theorem exp_eq_scalar_smul_residual
    {A : Type} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (a : ℝ) (X : A) :
    NormedSpace.exp X = Real.exp a • NormedSpace.exp (X - a • 1) := by
  let : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  have hc : Commute (a • (1 : A)) (X - a • 1) := by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      Algebra.commute_algebraMap_left a (X - a • 1)
  have he : NormedSpace.exp (a • (1 : A)) = Real.exp a • (1 : A) := by
    simpa only [Real.exp_eq_exp_ℝ, Algebra.algebraMap_eq_smul_one] using
      (NormedSpace.algebraMap_exp_comm (𝕂 := ℝ) (𝔸 := A) a).symm
  conv_lhs => rw [show X = a • 1 + (X - a • 1) by module]
  rw [NormedSpace.exp_add_of_commute hc, he, smul_mul_assoc, one_mul]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanResidualBounds
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounds for the actual residual automorphism

We identify the residual automorphism on a nonzero root with the analytic
exponential already estimated there. This removes a separate bound premise
for the automorphisms constructed from the Cartan action.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieAlgebra LieModule
open scoped BigOperators

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : TriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra] (χ : Weight ℝ H L) (hχ : χ.IsNonZero)

attribute [local instance] OAI.PolycyclicRecognition.instNormedAddCommGroupSubtypeMemLieSubmoduleRealLieSubalgebraRootSpaceCoeWeight_solutions_1
attribute [local instance] OAI.PolycyclicRecognition.instNormedSpaceRealSubtypeMemLieSubmoduleLieSubalgebraRootSpaceCoeWeight_solutions_1
local instance instNontrivialSubtypeMemLieSubmoduleRealLieSubalgebraRootSpaceCoeWeight_solutions_1_r69c624_1 : Nontrivial (rootSpace H χ) :=
  (LieSubmodule.nontrivial_iff_ne_bot ℝ H L).mpr χ.genWeightSpace_ne_bot
set_option maxHeartbeats 1000000 in
/-- Inclusion intertwines the root residual operator and the actual ideal
derivation. -/
theorem rootInIdeal_residual_apply (h : H) (v : rootSpace H χ) :
    CartanWordModel.rootInIdeal χ hχ ((rootAction H χ h - χ h • 1) v) =
      cartanIdealResidualDerivation T H h (CartanWordModel.rootInIdeal χ hχ v) := by
  apply Subtype.ext
  change (((rootAction H χ h - χ h • 1) v : rootSpace H χ) : L) =
    cartanResidualDerivation T H h (v : L)
  rw [cartanResidualDerivation_apply_root T H h χ v.property]
  rfl

set_option maxHeartbeats 1000000 in
theorem rootInIdeal_residual_pow (h : H) (k : ℕ) (v : rootSpace H χ) :
    CartanWordModel.rootInIdeal χ hχ (((rootAction H χ h - χ h • 1) ^ k) v) =
      ((cartanIdealResidualDerivation T H h).toLinearMap ^ k)
        (CartanWordModel.rootInIdeal χ hχ v) := by
  induction k generalizing v with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, mul_apply_eq_comp, ih, rootInIdeal_residual_apply,
      pow_succ, Module.End.mul_apply]
    rfl

set_option maxHeartbeats 1000000 in
include T hχ in
/-- The ambient dimension also truncates the analytic root operator. -/
theorem rootResidual_pow_ambient_dim (h : H) :
    (rootAction H χ h - χ h • 1) ^ finrank ℝ L = 0 := by
  apply ContinuousLinearMap.ext
  intro v
  have hinj : Function.Injective (CartanWordModel.rootInIdeal χ hχ) := by
    intro x y hxy
    exact Subtype.ext (congrArg (fun z : cartanRootIdeal H => (z : L)) hxy)
  apply hinj
  rw [rootInIdeal_residual_pow T H χ hχ h (finrank ℝ L) v,
    cartanIdealResidualDerivation_pow_eq_zero T H h]
  simp

set_option maxHeartbeats 1000000 in
/-- The polynomial Lie automorphism agrees with the analytic root residual
exponential, so the earlier operator norm bounds apply to this automorphism. -/
theorem rootInIdeal_residual_exp (h : H) (v : rootSpace H χ) :
    CartanWordModel.rootInIdeal χ hχ ((NormedSpace.exp (rootAction H χ h - χ h • 1)) v) =
      cartanIdealResidualAutomorphism T H h (CartanWordModel.rootInIdeal χ hχ v) := by
  rw [exp_eq_finite_sum_of_pow_eq_zero _ (rootResidual_pow_ambient_dim T H χ hχ h),
    cartanIdealResidualAutomorphism_apply]
  simp only [sum_apply, smul_apply, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro k _
  rw [rootInIdeal_residual_pow]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RootRepresentation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Root distortion in a faithful integrated representation

The conjugation identity is proved from a Lie homomorphism into a normed
algebra and the ordinary exponential matching identities. It is not an
additional geometric hypothesis.
-/

noncomputable section

namespace PolycyclicRecognition

open LieAlgebra LieModule

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] rootNormedAddCommGroup rootNormedSpace rootNontrivial

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {A : Type} [NormedRing A] [NormedAlgebra ℝ A]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra] (χ : Weight ℝ H L)
  (j : L →ₗ⁅ℝ⁆ A)

theorem representedRootVector_intertwines (h : H) (v : rootSpace H χ) :
    representedRootVector H χ j (rootAction H χ h v) =
      adjointOperator (j h) (representedRootVector H χ j v) := by
  change j ⁅(h : L), (v : L)⁆ = j h * j v - j v * j h
  rw [j.map_lie, Ring.lie_def]

variable [CompleteSpace A]

/-- The restricted root action exponentiates to actual matrix conjugation. -/
theorem represented_root_flow (h : H) (t : ℝ) (v : rootSpace H χ) :
    representedRootVector H χ j ((NormedSpace.exp (t • rootAction H χ h)) v) =
      NormedSpace.exp (t • j h) * j v * NormedSpace.exp (-(t • j h)) := by
  have hi := exp_intertwine_apply (representedRootVector H χ j)
    (t • rootAction H χ h) (t • adjointOperator (j h)) (by
      intro v
      simp only [smul_apply, map_smul, representedRootVector_intertwines]) v
  rw [exp_smul_adjointOperator_apply] at hi
  exact hi

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanAdjointAction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full exponential Cartan action

The scalar dilation and the polynomial residual automorphism together give
the exponential of the actual adjoint action on every nonzero root. In a
compatible faithful representation this is conjugation, not an independently
assumed action on the nilpotent ideal.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieAlgebra LieModule

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : TriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

variable (χ : Weight ℝ H L) (hχ : χ.IsNonZero)

attribute [local instance] OAI.PolycyclicRecognition.instNormedAddCommGroupSubtypeMemLieSubmoduleRealLieSubalgebraRootSpaceCoeWeight_solutions_2
attribute [local instance] OAI.PolycyclicRecognition.instNormedSpaceRealSubtypeMemLieSubmoduleLieSubalgebraRootSpaceCoeWeight_solutions_2
local instance instNontrivialSubtypeMemLieSubmoduleRealLieSubalgebraRootSpaceCoeWeight_solutions_2_r69c624_1 : Nontrivial (rootSpace H χ) :=
  (LieSubmodule.nontrivial_iff_ne_bot ℝ H L).mpr χ.genWeightSpace_ne_bot
set_option maxHeartbeats 1000000 in
/-- The full action is the analytic adjoint exponential on each nonzero root. -/
theorem rootInIdeal_adjoint_exp (h : H) (v : rootSpace H χ) :
    CartanWordModel.rootInIdeal χ hχ ((NormedSpace.exp (rootAction H χ h)) v) =
      cartanIdealAdjointAutomorphism T H h (CartanWordModel.rootInIdeal χ hχ v) := by
  rw [exp_eq_scalar_smul_residual (χ h) (rootAction H χ h),
    smul_apply, map_smul, rootInIdeal_residual_exp T H χ hχ h v]
  apply Subtype.ext
  change Real.exp (χ h) •
      (cartanIdealResidualAutomorphism T H h (CartanWordModel.rootInIdeal χ hχ v) : L) =
    cartanWeightScale T H h _
  exact (cartanWeightScale_apply_root T H h χ
    (cartanIdealResidualAutomorphism_root_mem T H h χ _ v.property)).symm

section Representation

variable {A : Type} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

attribute [local instance 100] LieRing.ofAssociativeRing

attribute [local instance] OAI.PolycyclicRecognition.instNormedAddCommGroupSubtypeMemLieSubmoduleRealLieSubalgebraRootSpaceCoeWeight_solutions_2
attribute [local instance] OAI.PolycyclicRecognition.instNormedSpaceRealSubtypeMemLieSubmoduleLieSubalgebraRootSpaceCoeWeight_solutions_2
local instance instNontrivialSubtypeMemLieSubmoduleRealLieSubalgebraRootSpaceCoeWeight_solutions_2_r69c624_2 : Nontrivial (rootSpace H χ) :=
  (LieSubmodule.nontrivial_iff_ne_bot ℝ H L).mpr χ.genWeightSpace_ne_bot
set_option maxHeartbeats 1000000 in
/-- The constructed action agrees with conjugation in a compatible algebra
representation on every generating root. -/
theorem represented_adjoint_root (j : L →ₗ⁅ℝ⁆ A) (h : H) (v : rootSpace H χ) :
    j (cartanIdealAdjointAutomorphism T H h (CartanWordModel.rootInIdeal χ hχ v) : L) =
      NormedSpace.exp (j h) * j v * NormedSpace.exp (-j h) := by
  rw [← rootInIdeal_adjoint_exp T H χ hχ h v]
  have hh := represented_root_flow H χ j h 1 v
  simp only [one_smul] at hh
  exact hh

set_option maxHeartbeats 1000000 in
omit hχ χ in
/-- Lie generation extends the root calculation to every vector in the
nilpotent ideal. -/
theorem represented_adjoint_ideal (j : L →ₗ⁅ℝ⁆ A) (h : H) (x : cartanRootIdeal H) :
    j (cartanIdealAdjointAutomorphism T H h x : L) =
      NormedSpace.exp (j h) * j x * NormedSpace.exp (-j h) := by
  let u := algebraExpUnit (j h)
  change j (cartanIdealAdjointAutomorphism T H h x : L) =
    (u : A) * j x * (↑(u⁻¹) : A)
  have hx : x ∈ LieSubalgebra.lieSpan ℝ (cartanRootIdeal H) (cartanGeneratorPool H) := by
    rw [cartanGeneratorPool_lieSpan H T]
    trivial
  have hmul (a b : A) :
      ((u : A) * a * (↑(u⁻¹) : A)) * ((u : A) * b * (↑(u⁻¹) : A)) =
        (u : A) * (a * b) * (↑(u⁻¹) : A) := by
    calc
      _ = (u : A) * a * ((↑(u⁻¹) : A) * u) * b * (↑(u⁻¹) : A) := by
        simp only [mul_assoc]
      _ = _ := by simp only [Units.inv_mul, mul_one, mul_assoc]
  induction hx using LieSubalgebra.lieSpan_induction with
  | mem x hx =>
    obtain ⟨ψ, hψ, hx⟩ := hx
    have he : CartanWordModel.rootInIdeal ψ hψ ⟨x, hx⟩ = x := Subtype.ext rfl
    have hh := represented_adjoint_root T H ψ hψ j h ⟨x, hx⟩
    rw [he] at hh
    exact hh
  | zero => simp only [map_zero, ZeroMemClass.coe_zero, mul_zero, zero_mul]
  | add x y _ _ hx hy =>
    simpa only [map_add, AddMemClass.coe_add, mul_add, add_mul] using congrArg₂ (· + ·) hx hy
  | smul a x _ hx =>
    simpa only [map_smul, SetLike.val_smul, smul_mul_assoc, mul_smul_comm,
      RingHom.id_apply] using congrArg (a • ·) hx
  | lie x y _ _ hx hy =>
    rw [LieEquiv.map_lie]
    change j ⁅(cartanIdealAdjointAutomorphism T H h x : L),
      (cartanIdealAdjointAutomorphism T H h y : L)⁆ =
        (u : A) * j ⁅(x : L), (y : L)⁆ * (↑(u⁻¹) : A)
    rw [j.map_lie, j.map_lie, hx, hy]
    simp only [Ring.lie_def, mul_sub, sub_mul, hmul]

end Representation

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanActualConjugation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual Cartan conjugation and shifted boxes

The full Lie action integrates to the nilpotent group. A faithful compatible
representation identifies this automorphism with ambient conjugation. The
resulting box estimate retains the polynomial residual factor and the exact
canonical-height translation.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule
open scoped Manifold

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {n : ℕ} (T : TriangularAdjoint L n)
  {EN N : Type} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  [FiniteDimensional ℝ EN] [TopologicalSpace N] [ChartedSpace EN N] [Group N]
  [LieGroup (𝓘(ℝ, EN)) ⊤ N] [T2Space N]
  (eN : cartanRootIdeal H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EN)) N)
  (Exp : GroupLieAlgebra (𝓘(ℝ, EN)) N → N) (hExp : IsGroupExponential Exp)
  (hbij : Function.Bijective Exp) (dynkin : NilpotentDynkinExpansionInput EN N)

section Representation

variable {A G : Type} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [Group G]

attribute [local instance 100] LieRing.ofAssociativeRing

set_option maxHeartbeats 1000000 in
/-- Compatibility of exponentials in a faithful representation identifies
the constructed automorphism with actual ambient conjugation. -/
theorem adjointGroupAutomorphism_eq_conjugation
    (j : L →ₗ⁅ℝ⁆ A) (ρ : G →* Aˣ) (hρ : Function.Injective ρ)
    (ι : N →* G) (d : H → G)
    (hN : ∀ x : cartanRootIdeal H, ρ (ι (Exp (eN x))) = algebraExpUnit (j x))
    (hd : ∀ h, ρ (d h) = algebraExpUnit (j h)) (h : H) (g : N) :
    ι (M.adjointGroupAutomorphism T eN Exp hExp hbij dynkin h g) =
      d h * ι g * (d h)⁻¹ := by
  obtain ⟨x, rfl⟩ := (hbij.comp eN.bijective).surjective g
  apply hρ
  change ρ (ι (integrateNilpotentLieEquiv eN Exp hbij dynkin hExp M.bound_zero
    (cartanIdealAdjointAutomorphism T H h) (Exp (eN x)))) = _
  rw [integrateNilpotentLieEquiv_apply_exp, hN, map_mul, map_mul, map_inv, hd]
  change algebraExpUnit (j (cartanIdealAdjointAutomorphism T H h x : L)) =
    algebraExpUnit (j h) * ρ (ι (Exp (eN x))) * (algebraExpUnit (j h))⁻¹
  rw [hN]
  rw [represented_adjoint_ideal T H j h x]
  exact algebraExpUnit_conj (algebraExpUnit (j h)) (j x)

end Representation

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanWordLogarithms
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cartan logarithms of bounded words

The Cartan group is nilpotent. The finite Dynkin identity therefore gives a
polynomial bound on the logarithm of every prefix of a bounded word. We also
record the exact semidirect-product word formula used to apply the controlled
Cartan estimates to such prefixes.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule
open scoped Manifold

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]
  {ED D : Type} [NormedAddCommGroup ED] [NormedSpace ℝ ED]
  [FiniteDimensional ℝ ED] [TopologicalSpace D] [ChartedSpace ED D] [Group D]
  [LieGroup (𝓘(ℝ, ED)) ⊤ D] [T2Space D]
  (eD : H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, ED)) D)
  (ExpD : GroupLieAlgebra (𝓘(ℝ, ED)) D → D) (hbijD : Function.Bijective ExpD)

set_option maxHeartbeats 1000000 in
omit [FiniteDimensional ℝ L] [H.IsCartanSubalgebra] [T2Space D] in
theorem exp_cartanLog (d : D) : ExpD (eD (cartanLog H eD ExpD hbijD d)) = d := by
  unfold cartanLog
  rw [eD.apply_symm_apply]
  exact (Equiv.ofBijective ExpD hbijD).apply_symm_apply d

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanSemidirectWords
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Controlled words in the actual semidirect product

Nilpotent Cartan increments give polynomial bounds on every Cartan prefix.
The exact semidirect-product formula then reduces its nilpotent coordinate
to the controlled product estimate. No polynomial bound on prefixes is left
as an assumption of this theorem.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule
open scoped Manifold

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {n : ℕ} (T : TriangularAdjoint L n)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  {EN N : Type} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  [FiniteDimensional ℝ EN] [TopologicalSpace N] [ChartedSpace EN N] [Group N]
  [LieGroup (𝓘(ℝ, EN)) ⊤ N] [T2Space N]
  (eN : cartanRootIdeal H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EN)) N)
  (ExpN : GroupLieAlgebra (𝓘(ℝ, EN)) N → N) (hExpN : IsGroupExponential ExpN)
  (hbijN : Function.Bijective ExpN) (dynkinN : NilpotentDynkinExpansionInput EN N)
  {ED D : Type} [NormedAddCommGroup ED] [NormedSpace ℝ ED]
  [FiniteDimensional ℝ ED] [TopologicalSpace D] [ChartedSpace ED D] [Group D]
  [LieGroup (𝓘(ℝ, ED)) ⊤ D] [T2Space D]
  (eD : H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, ED)) D)
  (ExpD : GroupLieAlgebra (𝓘(ℝ, ED)) D → D) (hExpD : IsGroupExponential ExpD)
  (hbijD : Function.Bijective ExpD) (dynkinD : NilpotentDynkinExpansionInput ED D)
  (φ : D →* MulAut N)

section Representation

variable {A G : Type} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [Group G]

attribute [local instance 100] LieRing.ofAssociativeRing

set_option maxHeartbeats 1000000 in
omit [T2Space D] in
/-- The required semidirect action identity follows from compatible
exponentials in an ambient faithful representation. -/
theorem action_eq_adjoint_of_representation
    (j : L →ₗ⁅ℝ⁆ A) (ρ : G →* Aˣ) (hρ : Function.Injective ρ)
    (ιN : N →* G) (hιN : Function.Injective ιN) (ιD : D →* G)
    (hconj : ∀ d g, ιN (φ d g) = ιD d * ιN g * (ιD d)⁻¹)
    (hN : ∀ x : cartanRootIdeal H, ρ (ιN (ExpN (eN x))) = algebraExpUnit (j x))
    (hD : ∀ h : H, ρ (ιD (ExpD (eD h))) = algebraExpUnit (j h)) (d : D) :
    φ d = M.adjointGroupAutomorphism T eN ExpN hExpN hbijN dynkinN
      (cartanLog H eD ExpD hbijD d) := by
  apply MulEquiv.ext
  intro g
  apply hιN
  rw [hconj]
  have hh := M.adjointGroupAutomorphism_eq_conjugation T eN ExpN hExpN hbijN dynkinN
    j ρ hρ ιN (fun h => ιD (ExpD (eD h))) hN hD (cartanLog H eD ExpD hbijD d) g
  simpa only [exp_cartanLog] using hh.symm

end Representation

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RayTangentContraction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ray contraction in the actual tangent coordinate basis -/
noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule Set
open scoped Manifold

namespace CartanWordModel
variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)

theorem coneAdjoint_projection
    (C : Set (H →ₗ[ℝ] ℝ)) (hadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C)
    (h : H) (x : cartanRootIdeal H) :
    M.coneAdjointAutomorphism T C hadd h (M.coneProjection C x) =
      M.coneProjection C (cartanIdealAdjointAutomorphism T H h x) := rfl

end CartanWordModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanRayFactorContraction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact increments and contraction for the actual Cartan factors -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set
open scoped Manifold

variable {EG G : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

variable (α₀ : H →ₗ[ℝ] ℝ)
  (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal (positiveWeightRay α₀)))
  (ExpQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier → Q.carrier)
  (hbijQ : Function.Bijective ExpQ)
  (chartQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier ≃ₜ Q.carrier)
  (hchartQ : ∀ v, chartQ v = ExpQ v)
  (hbijN : Function.Bijective F.ExpN) (hbijD : Function.Bijective F.ExpD)
  (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
  (π : F.N.carrier →* Q.carrier)
  (hπ : ∀ x : cartanRootIdeal H,
    π (F.ExpN (F.N.equiv x)) = ExpQ (Q.equiv (M.coneProjection (positiveWeightRay α₀) x)))
  (α : F.D.carrier →* MulAut Q.carrier)
  (hα : ∀ d n, α d (π n) = π (F.action d n))
  (hφ : ∀ d, F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN
    hbijN dynkinN (cartanLog H F.D.equiv F.ExpD hbijD d))

set_option maxHeartbeats 1000000 in
include hπ hα hφ in
/-- The quotient action of each actual Cartan factor is the exponential
of its induced Lie action, with the actual Cartan logarithm. -/
theorem factor_quotient_action_eq_exponential (d : F.D.carrier) (q : Q.carrier) :
    α d q = exponentialConjugate Q.equiv ExpQ hbijQ
      (M.coneAdjointAutomorphism T (positiveWeightRay α₀) (positiveWeightRay_add α₀)
        (cartanLog H F.D.equiv F.ExpD hbijD d)) q := by
  obtain ⟨v, hv⟩ := hbijQ.surjective q
  obtain ⟨w, hw⟩ := Q.equiv.surjective v
  obtain ⟨x, hx⟩ := M.coneProjection_surjective (positiveWeightRay α₀) w
  have hq : ExpQ (Q.equiv (M.coneProjection (positiveWeightRay α₀) x)) = q :=
    (congrArg ExpQ ((congrArg Q.equiv hx).trans hw)).trans hv
  rw [← hq]
  let h := cartanLog H F.D.equiv F.ExpD hbijD d
  have he : F.action d (F.ExpN (F.N.equiv x)) =
      F.ExpN (F.N.equiv (cartanIdealAdjointAutomorphism T H h x)) := by
    exact (congrArg (fun a : MulAut F.N.carrier => a (F.ExpN (F.N.equiv x)))
      (hφ d)).trans (integrateNilpotentLieEquiv_apply_exp F.N.equiv F.ExpN hbijN dynkinN
        F.isExpN M.bound_zero (cartanIdealAdjointAutomorphism T H h) x)
  calc
    α d (ExpQ (Q.equiv (M.coneProjection (positiveWeightRay α₀) x))) =
        α d (π (F.ExpN (F.N.equiv x))) := congrArg (α d) (hπ x).symm
    _ = π (F.action d (F.ExpN (F.N.equiv x))) := hα d _
    _ = π (F.ExpN (F.N.equiv (cartanIdealAdjointAutomorphism T H h x))) := congrArg π he
    _ = ExpQ (Q.equiv (M.coneProjection (positiveWeightRay α₀)
        (cartanIdealAdjointAutomorphism T H h x))) := hπ _
    _ = _ := by
      have hp := M.coneAdjoint_projection T (positiveWeightRay α₀)
        (positiveWeightRay_add α₀) h x
      exact (congrArg (fun v => ExpQ (Q.equiv v)) hp).symm.trans
        (exponentialConjugate_apply_exp Q.equiv ExpQ hbijQ
          (M.coneAdjointAutomorphism T (positiveWeightRay α₀)
            (positiveWeightRay_add α₀) h) (M.coneProjection (positiveWeightRay α₀) x)).symm

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanBoundaryContinuity
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Continuity of the constructed Cartan ray limits -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Filter Set
open scoped Manifold Topology

variable {EG G W : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsIsometricSMul G G] [ProperSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) (height : G →* Multiplicative W)
  (hheight : ∀ x, (height (ExpG x)).toAdd = eW (heightProjection T.character x))
  (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
  (hchartN : ∀ x, chartN x = F.ExpN x)
  (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
  (hchartD : ∀ x, chartD x = F.ExpD x)
  (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
  (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)

set_option maxHeartbeats 1000000 in
include hunimod hheight dynkinD in
/-- Uniform summable logarithmic increments on compact parameter sets make
an already constructed boundary ray limit continuous. -/
theorem continuous_boundary_ray_limit
    (hExpG : IsGroupExponential ExpG)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (γ₀ : M.Bases)
    (hφ : ∀ d, F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN
      (by rw [← show chartN = F.ExpN from funext hchartN]; exact chartN.bijective) dynkinN
      (cartanLog H F.D.equiv F.ExpD
        (by rw [← show chartD = F.ExpD from funext hchartD]; exact chartD.bijective) d))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {Kheight : ℝ} (hKheight : 0 ≤ Kheight)
    (hLip : ∀ x y, ‖(height x).toAdd - (height y).toAdd‖ ≤ Kheight * dist x y)
    (αW : W →L[ℝ] ℝ)
    (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal
      (positiveWeightRay (αW.toLinearMap.comp
        (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype))))))
    (ExpQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier → Q.carrier)
    (hExpQ : IsGroupExponential ExpQ)
    (chartQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier ≃ₜ Q.carrier)
    (hchartQ : ∀ v, chartQ v = ExpQ v)
    (dynkinQ : NilpotentDynkinExpansionInput Q.modelSpace Q.carrier)
    (π : F.N.carrier →* Q.carrier) (hπcont : Continuous π)
    (hπ : ∀ x : cartanRootIdeal H, π (F.ExpN (F.N.equiv x)) =
      ExpQ (Q.equiv (M.coneProjection (positiveWeightRay (αW.toLinearMap.comp
        (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype)))) x)))
    (α : F.D.carrier →* MulAut Q.carrier) (act : G →* Equiv.Perm Q.carrier)
    (hα : ∀ d n, α d (π n) = π (F.action d n))
    (hact : ∀ u d q, act (F.inclusionN u * F.inclusionD d) q = π u * α d q)
    (A : W →L[ℝ] W) (f : G → G) (hfcont : Continuous f)
    {L error : ℝ} (hL : 0 ≤ L)
    (hf : ∀ x y, dist (f x) (f y) ≤ L * dist x y + error)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ p g,
      ‖(height ((f p)⁻¹ * f (p * g))).toAdd - A ((height g).toAdd)‖ ≤ ε * dist 1 g + B)
    (v₀ : W) (hv₀ : αW (A v₀) < 0)
    (s : Q.carrier → F.N.carrier) (hs : Continuous s)
    (hsection : Function.RightInverse s π)
    (b : G → Q.carrier)
    (hlimit : ∀ x, Tendsto (fun n : ℕ => act (f (x *
      ExpG ((n : ℝ) • (cartanHeightSection T H (eW.symm v₀) :
        GroupLieAlgebra (𝓘(ℝ, EG)) G)))) 1) atTop (𝓝 (b x))) :
    Continuous b := by
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  have horbit := (F.orbitMap_isQuotientMap π hπcont s hs hsection α act hact).continuous
  apply continuous_from_compactlyGeneratedSpace b
  intro P _ _ _ center hcenter
  have hc : IsCompact (Set.range (f ∘ center)) := isCompact_range (hfcont.comp hcenter)
  obtain ⟨start, hstart⟩ := (Metric.isBounded_iff_subset_closedBall (1 : G)).mp hc.isBounded
  have hbound (p : P) : dist 1 (f (center p)) ≤ start := by
    have hh := hstart (Set.mem_range_self p)
    simpa only [Function.comp_apply, Metric.mem_closedBall, dist_comm] using hh
  have hfamily := bounded_family_height_of_centered_uniform height A f hKheight hLip hsub center hbound
  have hcoarse (p : P) (x y : G) :
      dist (f (center p * x)) (f (center p * y)) ≤ L * dist x y + error := by
    simpa only [dist_mul_left] using hf (center p * x) (center p * y)
  have hinitial (p : P) : dist 1 (f (center p * 1)) ≤ start := by
    simpa only [mul_one] using hbound p
  have hcontinuous (n : ℕ) : Continuous (fun p => act (f (center p *
      ExpG ((n : ℝ) • (cartanHeightSection T H (eW.symm v₀) :
        GroupLieAlgebra (𝓘(ℝ, EG)) G)))) 1) :=
    horbit.comp (hfcont.comp (hcenter.mul continuous_const))
  obtain ⟨g, K, hK, hg, hgK, hglimit⟩ := M.continuous_bounded_ray_quotient_limits
    T F hunimod eW height hheight chartN hchartN chartD hchartD dynkinN dynkinD
    b₀ γ₀ hφ hpath hKheight hLip αW Q ExpQ hExpQ chartQ hchartQ dynkinQ
    π hπcont hπ α act hα hact hExpG A (fun p x => f (center p * x))
    hinitial hL hcoarse hfamily v₀ hv₀ hcontinuous
  have he (p : P) : g p = b (center p) := tendsto_nhds_unique (hglimit p) (hlimit (center p))
  have hfunctions : g = b ∘ center := funext he
  rwa [hfunctions] at hg

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanBoundaryTopology
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Filter Set
open scoped Manifold Topology

variable {EG G W : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsIsometricSMul G G] [ProperSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) (height : G →* Multiplicative W)
  (hheight : ∀ x, (height (ExpG x)).toAdd = eW (heightProjection T.character x))
  (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
  (hchartN : ∀ x, chartN x = F.ExpN x)
  (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
  (hchartD : ∀ x, chartD x = F.ExpD x)
  (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
  (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)

set_option maxHeartbeats 1000000 in
include hunimod hheight dynkinD in
/-- The actual quotient topology descends continuity of the ray limit to
continuity of the boundary map. -/
theorem continuous_boundary_map_of_ray_limits
    (hExpG : IsGroupExponential ExpG)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (γ₀ : M.Bases)
    (hφ : ∀ d, F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN
      (by rw [← show chartN = F.ExpN from funext hchartN]; exact chartN.bijective) dynkinN
      (cartanLog H F.D.equiv F.ExpD
        (by rw [← show chartD = F.ExpD from funext hchartD]; exact chartD.bijective) d))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {Kheight : ℝ} (hKheight : 0 ≤ Kheight)
    (hLip : ∀ x y, ‖(height x).toAdd - (height y).toAdd‖ ≤ Kheight * dist x y)
    (αW : W →L[ℝ] ℝ)
    (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal
      (positiveWeightRay (αW.toLinearMap.comp
        (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype))))))
    (ExpQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier → Q.carrier)
    (hExpQ : IsGroupExponential ExpQ)
    (chartQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier ≃ₜ Q.carrier)
    (hchartQ : ∀ v, chartQ v = ExpQ v)
    (dynkinQ : NilpotentDynkinExpansionInput Q.modelSpace Q.carrier)
    (π : F.N.carrier →* Q.carrier) (hπcont : Continuous π)
    (hπ : ∀ x : cartanRootIdeal H, π (F.ExpN (F.N.equiv x)) =
      ExpQ (Q.equiv (M.coneProjection (positiveWeightRay (αW.toLinearMap.comp
        (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype)))) x)))
    (α : F.D.carrier →* MulAut Q.carrier) (act : G →* Equiv.Perm Q.carrier)
    (hα : ∀ d n, α d (π n) = π (F.action d n))
    (hact : ∀ u d q, act (F.inclusionN u * F.inclusionD d) q = π u * α d q)
    (A : W →L[ℝ] W) (f : G → G) (hfcont : Continuous f)
    {L error : ℝ} (hL : 0 ≤ L)
    (hf : ∀ x y, dist (f x) (f y) ≤ L * dist x y + error)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ p g,
      ‖(height ((f p)⁻¹ * f (p * g))).toAdd - A ((height g).toAdd)‖ ≤ ε * dist 1 g + B)
    (v₀ : W) (hv₀ : αW (A v₀) < 0)
    (s : Q.carrier → F.N.carrier) (hs : Continuous s)
    (hsection : Function.RightInverse s π)
    {S : Type} [Group S] [TopologicalSpace S]
    (πS : F.N.carrier →* S) (hπS : Continuous πS)
    (sS : S → F.N.carrier) (hsS : Continuous sS)
    (hsectionS : Function.RightInverse sS πS)
    (αS : F.D.carrier →* MulAut S) (actS : G →* Equiv.Perm S)
    (hactS : ∀ u d q, actS (F.inclusionN u * F.inclusionD d) q = πS u * αS d q)
    (B : S → Q.carrier)
    (hlimit : ∀ x, Tendsto (fun n : ℕ => act (f (x *
      ExpG ((n : ℝ) • (cartanHeightSection T H (eW.symm v₀) :
        GroupLieAlgebra (𝓘(ℝ, EG)) G)))) 1) atTop (𝓝 (B (actS x 1)))) :
    Continuous B := by
  have hb := M.continuous_boundary_ray_limit T F hunimod eW height hheight
    chartN hchartN chartD hchartD dynkinN dynkinD hExpG
    b₀ γ₀ hφ hpath hKheight hLip αW Q ExpQ hExpQ chartQ hchartQ dynkinQ
    π hπcont hπ α act hα hact A f hfcont hL hf hsub v₀ hv₀
    s hs hsection (fun x => B (actS x 1)) hlimit
  exact (F.orbitMap_isQuotientMap πS hπS sS hsS hsectionS αS actS hactS).continuous_iff.mpr hb

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanRayActionTopology
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Continuity of the actual ray quotient action -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set
open scoped Manifold

variable {EG G : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

variable (α₀ : H →ₗ[ℝ] ℝ)
  (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal (positiveWeightRay α₀)))
  (ExpQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier → Q.carrier)
  (hbijQ : Function.Bijective ExpQ)
  (chartQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier ≃ₜ Q.carrier)
  (hchartQ : ∀ v, chartQ v = ExpQ v)
  (hbijN : Function.Bijective F.ExpN) (hbijD : Function.Bijective F.ExpD)
  (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
  (π : F.N.carrier →* Q.carrier)
  (hπ : ∀ x : cartanRootIdeal H,
    π (F.ExpN (F.N.equiv x)) = ExpQ (Q.equiv (M.coneProjection (positiveWeightRay α₀) x)))
  (α : F.D.carrier →* MulAut Q.carrier)
  (hα : ∀ d n, α d (π n) = π (F.action d n))
  (hφ : ∀ d, F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN
    hbijN dynkinN (cartanLog H F.D.equiv F.ExpD hbijD d))

set_option maxHeartbeats 1000000 in
include hbijQ hchartQ hπ hα hφ in
/-- Each actual Cartan factor acts continuously on the ray quotient.
This follows from its previously identified exponential conjugation. -/
theorem continuous_ray_factor_action (d : F.D.carrier) : Continuous (α d) := by
  have heq : (α d : Q.carrier → Q.carrier) = exponentialConjugate Q.equiv ExpQ hbijQ
      (M.coneAdjointAutomorphism T (positiveWeightRay α₀) (positiveWeightRay_add α₀)
        (cartanLog H F.D.equiv F.ExpD hbijD d)) := by
    funext q
    exact M.factor_quotient_action_eq_exponential T F α₀ Q ExpQ hbijQ
      hbijN hbijD dynkinN π hπ α hα hφ d q
  rw [heq]
  exact continuous_exponentialConjugate Q.equiv ExpQ hbijQ chartQ hchartQ _

set_option maxHeartbeats 1000000 in
include hbijQ hchartQ hπ hα hφ in
/-- Every fixed ambient group element acts continuously; no continuity
assumption on a chosen factorization is needed. -/
theorem continuous_ambient_ray_action
    (act : G →* Equiv.Perm Q.carrier)
    (hact : ∀ u d q, act (F.inclusionN u * F.inclusionD d) q = π u * α d q)
    (g : G) : Continuous (act g) := by
  let _ : IsTopologicalGroup Q.carrier := topologicalGroup_of_lieGroup (𝓘(ℝ, Q.modelSpace)) ⊤
  obtain ⟨⟨u, d⟩, he⟩ := F.surjective g
  have heq : (act g : Q.carrier → Q.carrier) = fun q => π u * α d q := by
    funext q
    rw [← he]
    exact hact u d q
  rw [heq]
  exact continuous_const.mul (M.continuous_ray_factor_action T F α₀ Q ExpQ hbijQ
    chartQ hchartQ hbijN hbijD dynkinN π hπ α hα hφ d)

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialRepresentationInput
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exponential compatibility in the published faithful realization

Onshuus–Post (2022), Proposition 2.4 and proof, give a faithful inducing
linear Lie realization of a simply connected real triangular group.
Lee, *Introduction to Smooth Manifolds*, second edition (2013), Theorem 8.44
(p.195) and Proposition 20.8(g) (p.520), give its Lie algebra map and
exponential compatibility. Only these properties are retained below.

https://doi.org/10.1112/blms.12574
https://doi.org/10.1007/978-1-4419-9982-5

The action and all bounds remain proved consequences, not part of the input.
-/

noncomputable section

namespace PolycyclicRecognition

open scoped Manifold Matrix.Norms.Operator

attribute [local instance 100] LieRing.ofAssociativeRing

variable {EG G : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]

variable [SimplyConnectedSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

/-- The published representation identifies the actual factor action with
the explicit full Cartan adjoint automorphism. -/
theorem cartan_action_eq_adjoint_of_published_realization
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (hbijN : Function.Bijective F.ExpN) (hbijD : Function.Bijective F.ExpD)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (d : F.D.carrier) :
    F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN hbijN dynkinN
      (cartanLog H F.D.equiv F.ExpD hbijD d) := by
  obtain ⟨m, hm, ρ, j, hind, hExp⟩ := realize ⟨a, ⟨T⟩⟩ ExpG hExpG
  let _ : NeZero m := ⟨Nat.ne_of_gt hm⟩
  have hρ : Function.Injective ρ := by
    intro g h he
    exact hind.injective (congrArg (fun u : (Matrix (Fin m) (Fin m) ℝ)ˣ =>
      (u : Matrix (Fin m) (Fin m) ℝ)) he)
  exact M.action_eq_adjoint_of_representation T F.N.equiv F.ExpN F.isExpN hbijN dynkinN
    F.D.equiv F.ExpD hbijD F.action j ρ hρ F.inclusionN F.closedN.injective F.inclusionD
    F.conjugation (fun x => by rw [F.compatibleN, hExp])
    (fun x => by rw [F.compatibleD, hExp]) d

open Module LieAlgebra LieModule

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanRayBoundaryModel
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete ray quotients and their ambient actions

The model is chosen from the previously stated nilpotent existence,
integration, and Haar inputs. Its action, section, topology and contraction
are proved properties of that choice.
-/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Filter TopologicalSpace Topology
open scoped Manifold Topology

variable {EG G : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (α₀ : H →ₗ[ℝ] ℝ)

namespace RayBoundaryModel

variable {M F α₀} (R : M.RayBoundaryModel F α₀)

set_option maxHeartbeats 1000000 in
theorem continuous_sectionMap : Continuous R.sectionMap :=
  F.closedN.continuous.comp R.cone.maps.sectionMap.continuous

set_option maxHeartbeats 1000000 in
theorem section_rightInverse (q : R.cone.Q.carrier) : R.action (R.sectionMap q) 1 = q := by
  have h := R.action_eq (R.cone.maps.sectionMap q) 1 1
  simpa only [sectionMap, map_one, mul_one, R.cone.maps.section_rightInverse] using h

set_option maxHeartbeats 1000000 in
theorem orbit_surjective : Function.Surjective (fun g => R.action g 1) :=
  fun q => ⟨R.sectionMap q, R.section_rightInverse q⟩

variable {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  [SimplyConnectedSpace G]
  (hExpG : IsGroupExponential ExpG)
  (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
  (hbijN : Function.Bijective F.ExpN) (hbijD : Function.Bijective F.ExpD)
  (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)

set_option maxHeartbeats 1000000 in
include T hExpG realize hbijN hbijD dynkinN in
theorem continuous_action (g : G) : Continuous (R.action g) := by
  exact M.continuous_ambient_ray_action T F α₀ R.cone.Q R.cone.maps.expQ
    (by rw [← show R.cone.maps.chartQ = R.cone.maps.expQ from
      funext R.cone.maps.chartQ_eq]; exact R.cone.maps.chartQ.bijective)
    R.cone.maps.chartQ R.cone.maps.chartQ_eq hbijN hbijD dynkinN
    R.cone.maps.quotient R.cone.maps.quotient_exp R.factorAction R.equivariant
    (fun d => cartan_action_eq_adjoint_of_published_realization
      T M F hExpG realize hbijN hbijD dynkinN d) R.action R.action_eq g

end RayBoundaryModel

open scoped Matrix.Norms.Operator
attribute [local instance 100] LieRing.ofAssociativeRing

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanRayBoundaryFamily
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Continuous boundary families on the concrete ray quotients -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Filter Set
open scoped Manifold Topology

variable {EG G W P : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsIsometricSMul G G] [ProperSpace G]
  [SimplyConnectedSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) (height : G →* Multiplicative W)
  (hheight : ∀ x, (height (ExpG x)).toAdd = eW (heightProjection T.character x))
  (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
  (hchartN : ∀ x, chartN x = F.ExpN x)
  (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
  (hchartD : ∀ x, chartD x = F.ExpD x)
  (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
  (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)

set_option maxHeartbeats 1000000 in
include hunimod hheight chartN hchartN chartD hchartD dynkinN dynkinD in
/-- For concrete source and target ray quotients, the uniform sublinear
estimate constructs continuous boundary maps with a common compact shadow. -/
theorem exists_continuous_ray_boundary_family
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (γ₀ : M.Bases)
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {Kheight : ℝ} (hKheight : 0 ≤ Kheight)
    (hLip : ∀ x y, ‖(height x).toAdd - (height y).toAdd‖ ≤ Kheight * dist x y)
    (αS αT : W →L[ℝ] ℝ) (A : W →L[ℝ] W) (hα : αS = αT.comp A)
    (RS : M.RayBoundaryModel F (αS.toLinearMap.comp
      (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype))))
    (RT : M.RayBoundaryModel F (αT.toLinearMap.comp
      (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype))))
    (dynkinT : NilpotentDynkinExpansionInput RT.cone.Q.modelSpace RT.cone.Q.carrier)
    (f : P → G → G) (hcont : ∀ p, Continuous (f p))
    {L error : ℝ} (hL : 0 ≤ L)
    (hf : ∀ p x y, dist (f p x) (f p y) ≤ L * dist x y + error)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ p x g,
      ‖(height ((f p x)⁻¹ * f p (x * g))).toAdd - A ((height g).toAdd)‖ ≤
        ε * dist 1 g + B)
    (v₀ : W) (hv₀ : αT (A v₀) < 0) :
    Nonempty (BoundaryMapFamily RS.action RT.action f) := by
  subst αS
  have hbijN : Function.Bijective F.ExpN := by
    rw [← show chartN = F.ExpN from funext hchartN]
    exact chartN.bijective
  have hbijD : Function.Bijective F.ExpD := by
    rw [← show chartD = F.ExpD from funext hchartD]
    exact chartD.bijective
  have hφ := fun d => cartan_action_eq_adjoint_of_published_realization
    T M F hExpG realize hbijN hbijD dynkinN d
  obtain ⟨B, K, hK, hB⟩ := M.exists_boundary_family_with_compact_shadow
    T F hunimod eW height hheight chartN hchartN chartD hchartD dynkinN dynkinD
    hExpG realize haarN haarD b₀ γ₀ hφ hpath hKheight hLip
    αT RT.cone.Q RT.cone.maps.expQ RT.cone.maps.isExpQ
    RT.cone.maps.chartQ RT.cone.maps.chartQ_eq dynkinT
    RT.cone.maps.quotient RT.cone.maps.quotient_continuous RT.cone.maps.quotient_exp
    RT.factorAction RT.action RT.equivariant RT.action_eq
    A f hL hf hsub v₀ hv₀ RS.cone.maps.quotient RS.action
    RS.cone.maps.kernel_eq RS.stabilizer RS.orbit_surjective
  refine ⟨⟨B, K, hK, ?_, fun p x => (hB p x).2⟩⟩
  intro p
  apply M.continuous_boundary_map_of_ray_limits
    T F hunimod eW height hheight chartN hchartN chartD hchartD dynkinN dynkinD
    hExpG b₀ γ₀ hφ hpath hKheight hLip
    αT RT.cone.Q RT.cone.maps.expQ RT.cone.maps.isExpQ
    RT.cone.maps.chartQ RT.cone.maps.chartQ_eq dynkinT
    RT.cone.maps.quotient RT.cone.maps.quotient_continuous RT.cone.maps.quotient_exp
    RT.factorAction RT.action RT.equivariant RT.action_eq A (f p) (hcont p) hL (hf p)
    (fun ε hε => by
      obtain ⟨D, hD, hb⟩ := hsub ε hε
      exact ⟨D, hD, hb p⟩) v₀ hv₀
    RT.cone.maps.sectionMap RT.cone.maps.sectionMap.continuous RT.cone.maps.section_rightInverse
    RS.cone.maps.quotient RS.cone.maps.quotient_continuous
    RS.cone.maps.sectionMap RS.cone.maps.sectionMap.continuous RS.cone.maps.section_rightInverse
    RS.factorAction RS.action RS.action_eq (B p)
  exact fun x => (hB p x).1

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanRayBoundaryInverse
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Inverse boundary families on concrete Cartan quotients -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set
open scoped Manifold

variable {EG G P : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsIsometricSMul G G] [ProperSpace G]
  [SimplyConnectedSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

set_option maxHeartbeats 1000000 in
include T in
/-- The actual quotient contraction supplies both inverse identities. -/
theorem ray_boundary_homeomorphisms_of_compact_shadows
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (hbijN : Function.Bijective F.ExpN) (hbijD : Function.Bijective F.ExpD)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (αS αT : H →ₗ[ℝ] ℝ) (RS : M.RayBoundaryModel F αS) (RT : M.RayBoundaryModel F αT)
    (vS vT : H) (hvS : αS vS < 0) (hvT : αT vT < 0)
    (B : P → RS.cone.Q.carrier → RT.cone.Q.carrier)
    (C : P → RT.cone.Q.carrier → RS.cone.Q.carrier)
    (hBcont : ∀ p, Continuous (B p)) (hCcont : ∀ p, Continuous (C p))
    (f g : P → G → G) {Lf Lg ef eg E : ℝ} (hLf : 0 ≤ Lf) (hLg : 0 ≤ Lg)
    (hf : ∀ p x y, dist (f p x) (f p y) ≤ Lf * dist x y + ef)
    (hg : ∀ p x y, dist (g p x) (g p y) ≤ Lg * dist x y + eg)
    (hgf : ∀ p x, dist (g p (f p x)) x ≤ E)
    (hfg : ∀ p x, dist (f p (g p x)) x ≤ E)
    (KS : Set RS.cone.Q.carrier) (KT : Set RT.cone.Q.carrier)
    (hKS : IsCompact KS) (hKT : IsCompact KT)
    (hB : ∀ p x, ∃ z ∈ KT, B p (RS.action x 1) = RT.action (f p x) z)
    (hC : ∀ p x, ∃ z ∈ KS, C p (RT.action x 1) = RS.action (g p x) z) :
    ∃ D : P → RS.cone.Q.carrier ≃ₜ RT.cone.Q.carrier,
      (∀ p q, D p q = B p q) ∧ (∀ p q, (D p).symm q = C p q) := by
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  obtain ⟨hfixS, hcS⟩ := RS.contracts_compact_orbits_m T hExpG realize hbijN hbijD dynkinN vS hvS
  obtain ⟨hfixT, hcT⟩ := RT.contracts_compact_orbits_m T hExpG realize hbijN hbijD dynkinN vT hvT
  exact boundary_family_homeomorphisms_of_compact_shadows
    RS.action RT.action (RS.continuous_action T hExpG realize hbijN hbijD dynkinN)
    (RT.continuous_action T hExpG realize hbijN hbijD dynkinN)
    RS.sectionMap RS.continuous_sectionMap RS.section_rightInverse
    RT.sectionMap RT.continuous_sectionMap RT.section_rightInverse
    _ _ hfixS hfixT hcS hcT B C hBcont hCcont f g hLf hLg hf hg hgf hfg
    KS KT hKS hKT hB hC

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanRayBoundaryHomeomorphism
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual boundary homeomorphisms for coarse inverse families -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Filter Set
open scoped Manifold Topology

variable {EG G W P : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsIsometricSMul G G] [ProperSpace G]
  [SimplyConnectedSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) (height : G →* Multiplicative W)
  (hheight : ∀ x, (height (ExpG x)).toAdd = eW (heightProjection T.character x))
  (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
  (hchartN : ∀ x, chartN x = F.ExpN x)
  (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
  (hchartD : ∀ x, chartD x = F.ExpD x)
  (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
  (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)

set_option maxHeartbeats 1000000 in
include hunimod hheight chartN hchartN chartD hchartD dynkinN dynkinD in
/-- Applying the ray construction in both directions gives homeomorphisms,
with common compact forward and inverse shadows. -/
theorem exists_ray_boundary_family_homeomorphisms_oai
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (γ₀ : M.Bases)
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {Kheight : ℝ} (hKheight : 0 ≤ Kheight)
    (hLip : ∀ x y, ‖(height x).toAdd - (height y).toAdd‖ ≤ Kheight * dist x y)
    (αS αT : W →L[ℝ] ℝ) (A : W ≃L[ℝ] W)
    (hα : αS = αT.comp A.toContinuousLinearMap)
    (RS : M.RayBoundaryModel F (αS.toLinearMap.comp
      (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype))))
    (RT : M.RayBoundaryModel F (αT.toLinearMap.comp
      (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype))))
    (dynkinS : NilpotentDynkinExpansionInput RS.cone.Q.modelSpace RS.cone.Q.carrier)
    (dynkinT : NilpotentDynkinExpansionInput RT.cone.Q.modelSpace RT.cone.Q.carrier)
    (f g : P → G → G) (hfcont : ∀ p, Continuous (f p)) (hgcont : ∀ p, Continuous (g p))
    {Lf Lg ef eg E : ℝ} (hLf : 0 ≤ Lf) (hLg : 0 ≤ Lg)
    (hf : ∀ p x y, dist (f p x) (f p y) ≤ Lf * dist x y + ef)
    (hg : ∀ p x y, dist (g p x) (g p y) ≤ Lg * dist x y + eg)
    (hgf : ∀ p x, dist (g p (f p x)) x ≤ E)
    (hfg : ∀ p x, dist (f p (g p x)) x ≤ E)
    (hsubf : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ p x y,
      ‖(height ((f p x)⁻¹ * f p (x * y))).toAdd - A ((height y).toAdd)‖ ≤
        ε * dist 1 y + B)
    (hsubg : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ p x y,
      ‖(height ((g p x)⁻¹ * g p (x * y))).toAdd - A.symm ((height y).toAdd)‖ ≤
        ε * dist 1 y + B)
    (v₀ : W) (hv₀ : αS v₀ < 0) :
    ∃ (B : P → RS.cone.Q.carrier ≃ₜ RT.cone.Q.carrier)
      (KS : Set RS.cone.Q.carrier) (KT : Set RT.cone.Q.carrier),
      IsCompact KS ∧ IsCompact KT ∧
      (∀ p x, ∃ z ∈ KT, B p (RS.action x 1) = RT.action (f p x) z) ∧
      (∀ p x, ∃ z ∈ KS, (B p).symm (RT.action x 1) = RS.action (g p x) z) := by
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  have htarget : αT (A v₀) < 0 := by
    simpa only [hα, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe] using hv₀
  have hαinv : αT = αS.comp A.symm.toContinuousLinearMap := by
    rw [hα]
    ext w
    simp
  have hinverse : αS (A.symm (A v₀)) < 0 := by simpa using hv₀
  let forward : BoundaryMapFamily RS.action RT.action f := Classical.choice <|
    M.exists_continuous_ray_boundary_family
    T F hunimod eW height hheight chartN hchartN chartD hchartD dynkinN dynkinD
    hExpG realize haarN haarD b₀ γ₀ hpath hKheight hLip αS αT
    A.toContinuousLinearMap hα RS RT dynkinT f hfcont hLf hf hsubf v₀ htarget
  let inverse : BoundaryMapFamily RT.action RS.action g := Classical.choice <|
    M.exists_continuous_ray_boundary_family
    T F hunimod eW height hheight chartN hchartN chartD hchartD dynkinN dynkinD
    hExpG realize haarN haarD b₀ γ₀ hpath hKheight hLip αT αS
    A.symm.toContinuousLinearMap hαinv RT RS dynkinS g hgcont hLg hg hsubg (A v₀) hinverse
  have hbijN : Function.Bijective F.ExpN := by
    rw [← show chartN = F.ExpN from funext hchartN]
    exact chartN.bijective
  have hbijD : Function.Bijective F.ExpD := by
    rw [← show chartD = F.ExpD from funext hchartD]
    exact chartD.bijective
  have hvS : (αS.toLinearMap.comp
      (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype)))
      (cartanHeightSection T H (eW.symm v₀)) < 0 := by
    change αS (eW (heightProjection T.character
      ((cartanHeightSection T H (eW.symm v₀) : H) : GroupLieAlgebra (𝓘(ℝ, EG)) G))) < 0
    simpa only [cartanHeightSection_height, LinearEquiv.apply_symm_apply] using hv₀
  have hvT : (αT.toLinearMap.comp
      (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype)))
      (cartanHeightSection T H (eW.symm (A v₀))) < 0 := by
    change αT (eW (heightProjection T.character
      ((cartanHeightSection T H (eW.symm (A v₀)) : H) : GroupLieAlgebra (𝓘(ℝ, EG)) G))) < 0
    simpa only [cartanHeightSection_height, LinearEquiv.apply_symm_apply] using htarget
  obtain ⟨D, hD, hDinv⟩ := M.ray_boundary_homeomorphisms_of_compact_shadows
    T F hExpG realize hbijN hbijD dynkinN _ _ RS RT
    (cartanHeightSection T H (eW.symm v₀))
    (cartanHeightSection T H (eW.symm (A v₀))) hvS hvT
    forward.map inverse.map forward.continuous inverse.continuous f g hLf hLg hf hg hgf hfg
    inverse.compact forward.compact inverse.isCompact forward.isCompact forward.shadow inverse.shadow
  refine ⟨D, inverse.compact, forward.compact, inverse.isCompact, forward.isCompact, ?_, ?_⟩
  · intro p x
    simpa only [hD] using forward.shadow p x
  · intro p x
    simpa only [hDinv] using inverse.shadow p x

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

theorem solution : type_of% @OAI.PolycyclicRecognition.CartanWordModel.exists_ray_boundary_family_homeomorphisms_oai := @OAI.PolycyclicRecognition.CartanWordModel.exists_ray_boundary_family_homeomorphisms_oai
