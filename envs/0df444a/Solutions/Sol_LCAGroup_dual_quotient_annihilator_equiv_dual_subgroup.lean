-- Prove2me | solution 1 for LCAGroup.dual_quotient_annihilator_equiv_dual_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:34:49.546912+00:00
-- url     : https://prove2.me/submissions/bfc61740-9dd7-4f88-9d8b-4d0e0204b859

import Mathlib
import Definitions.Def_LCAGroup_Annihilator
import Theorems.Thm_MasulloGRH_pontryaginDual_separates_of_locallyCompact

open Topology

set_option autoImplicit false

/-!
The dual of a closed subgroup: `Ĝ ⧸ H^⊥ ≃ₜ* Ĥ` (Lemma D.1.4.6(2), second isomorphism).

The argument follows the proof in the open formalization `mccorvie/riemann-masullo`
(`RiemannMasullo.lcaDualQuotient_equiv_subgroupDual` and the character-extension lemmas of its
`ForMathlib/Topology/Algebra/PontryaginDual*.lean`), with the separation of points by characters
taken from the platform theorem `MasulloGRH.pontryaginDual_separates_of_locallyCompact`.
-/

namespace Sol_LCAGroup_dual_quotient_annihilator_equiv_dual_subgroup

open MeasureTheory Set Filter Topology
open scoped ComplexConjugate Pointwise

/-! ### Separation of points -/

/-- Each nonidentity element of a locally compact Hausdorff abelian group is detected by a
continuous character. -/
theorem exists_pontryaginDual_apply_ne_one {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] {x : G} (hx : x ≠ 1) :
    ∃ χ : PontryaginDual G, χ x ≠ 1 := by
  obtain ⟨χ, -, hχ⟩ := MasulloGRH.pontryaginDual_separates_of_locallyCompact G ⊥
    (by rw [Subgroup.coe_bot]; exact isClosed_singleton) x
    (by rw [Subgroup.mem_bot]; exact hx)
  exact ⟨χ, hχ⟩

/-! ### Extension of characters from compact subgroups of compact groups -/

/-- Restricted characters separate points of the subgroup, so their complex linear span is
dense. -/
theorem dense_span_restrictedCharacters {H K : Type*}
    [CommGroup H] [TopologicalSpace H] [CompactSpace H]
    [CommGroup K] [TopologicalSpace K] [IsTopologicalGroup K] [T2Space K] [CompactSpace K]
    (i : H →ₜ* K) (hi : Function.Injective i)
    (r : PontryaginDual K →* C(H, ℂ)) (hr : ∀ ψ x, r ψ x = (ψ (i x) : ℂ)) :
    (Submodule.span ℂ (range r)).topologicalClosure = ⊤ := by
  let S := MonoidHom.mrange r
  let A := StarAlgebra.adjoin ℂ (S : Set C(H, ℂ))
  have hstar : star (S : Set C(H, ℂ)) ⊆ S := by
    rw [Set.star_subset]
    rintro _ ⟨ψ, rfl⟩
    refine ⟨ψ⁻¹, ContinuousMap.ext fun x ↦ ?_⟩
    change r ψ⁻¹ x = star (r ψ x)
    rw [hr, hr]
    exact Circle.coe_inv_eq_conj (ψ (i x))
  have hsep : A.SeparatesPoints := by
    intro x y hxy
    obtain ⟨ψ, hψ⟩ := exists_pontryaginDual_apply_ne_one (div_ne_one.mpr (hi.ne hxy))
    refine ⟨_, ⟨r ψ, StarAlgebra.subset_adjoin ℂ (S : Set C(H, ℂ)) ⟨ψ, rfl⟩, rfl⟩, ?_⟩
    change r ψ x ≠ r ψ y
    rw [hr, hr, Ne, Circle.coe_inj]
    exact fun he ↦ hψ ((map_div ψ _ _).trans (div_eq_one.mpr he))
  have hspan : A.toSubalgebra.toSubmodule = Submodule.span ℂ (range r) := by
    rw [StarAlgebra.adjoin_eq_span, Set.union_eq_left.mpr hstar, S.closure_eq]
    rfl
  rw [← hspan]
  exact congrArg (fun S : StarSubalgebra ℂ C(H, ℂ) ↦ S.toSubalgebra.toSubmodule)
    (ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints A hsep)

/-- A character of a compact subgroup of a compact Hausdorff abelian group extends to the
whole group. The subgroup is presented by an injective continuous homomorphism.
Stone–Weierstrass gives density of the span of the restricted characters. Orthogonality
on the subgroup then gives the desired restriction. -/
theorem exists_pontryaginDual_extension_of_compact {H K : Type*}
    [CommGroup H] [TopologicalSpace H] [CompactSpace H]
    [CommGroup K] [TopologicalSpace K] [IsTopologicalGroup K] [T2Space K] [CompactSpace K]
    (i : H →ₜ* K) (hi : Function.Injective i) (χ : PontryaginDual H) :
    ∃ ψ : PontryaginDual K, ∀ x, ψ (i x) = χ x := by
  classical
  have he := i.continuous.isClosedEmbedding hi
  let : T2Space H := he.isEmbedding.t2Space
  let : IsTopologicalGroup H := he.isEmbedding.isInducing.topologicalGroup i
  let : MeasurableSpace H := borel H
  let : BorelSpace H := ⟨rfl⟩
  let μ : Measure H := Measure.haar
  let r : PontryaginDual K →* C(H, ℂ) :=
    { toFun ψ := ⟨fun x ↦ (ψ (i x) : ℂ), continuous_subtype_val.comp (ψ.continuous.comp i.continuous)⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
  let c : C(H, ℂ) := ⟨fun x ↦ (χ x : ℂ), continuous_subtype_val.comp χ.continuous⟩
  -- The Fourier coefficient at χ is a continuous linear functional on continuous functions.
  let T := ContinuousMap.toLp (E := ℂ) 2 μ ℂ
  let L := (innerSL ℂ (T c)).comp T
  by_contra! hnone
  have horth : Submodule.span ℂ (range r) ≤ L.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨ψ, rfl⟩
    obtain ⟨g, hg⟩ := hnone ψ
    let δ : PontryaginDual H := PontryaginDual.map i ψ * χ⁻¹
    have hδ : (δ g : ℂ) ≠ 1 := by
      change ((ψ (i g) * (χ g)⁻¹ : Circle) : ℂ) ≠ 1
      rw [← div_eq_mul_inv]
      exact fun h ↦ hg (div_eq_one.mp (Circle.ext h))
    change inner ℂ (T c) (T (r ψ)) = 0
    rw [ContinuousMap.inner_toLp]
    change (∫ x, (ψ (i x) : ℂ) * conj (χ x : ℂ) ∂μ) = 0
    simp_rw [← Circle.coe_inv_eq_conj]
    change (∫ x, (δ x : ℂ) ∂μ) = 0
    -- Translation by g fixes the integral but multiplies it by the nontrivial value δ(g).
    have ht := integral_mul_left_eq_self (μ := μ) (fun x ↦ (δ x : ℂ)) g
    simp_rw [map_mul, Circle.coe_mul, integral_const_mul] at ht
    by_contra hn
    exact hδ ((mul_eq_right₀ hn).mp ht)
  have htop := (Submodule.span ℂ (range r)).topologicalClosure_minimal horth L.isClosed_ker
  rw [dense_span_restrictedCharacters i hi r (fun _ _ ↦ rfl)] at htop
  have hc : inner ℂ (T c) (T c) = 0 := htop (Submodule.mem_top (x := c))
  have hc0 := (ContinuousMap.toLp_injective (p := 2) (𝕜 := ℂ) μ)
    ((inner_self_eq_zero.mp hc).trans (map_zero T).symm)
  have : (1 : ℂ) = 0 := by simpa [c] using congrArg (fun f : C(H, ℂ) ↦ f 1) hc0
  exact one_ne_zero this

/-! ### Extension of characters from closed subgroups -/

section Restriction

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]

/-- A character of a compact group embedded in an LCA group extends to the whole group.
Evaluation embeds the compact group into the compact closure of the ambient evaluation image. -/
theorem exists_extension_of_compact_source {K : Type*} [CommGroup K]
    [TopologicalSpace K] [CompactSpace K] (i : K →ₜ* G) (hi : Function.Injective i)
    (χ : PontryaginDual K) : ∃ ψ : PontryaginDual G, ∀ x, ψ (i x) = χ x := by
  let ev : G →* (PontryaginDual G → Circle) :=
    { toFun x ψ := ψ x
      map_one' := funext fun ψ ↦ map_one ψ
      map_mul' x y := funext fun ψ ↦ map_mul ψ x y }
  have hev : Continuous ev := continuous_pi fun ψ ↦ ψ.continuous
  have hinj : Function.Injective ev := by
    intro x y h
    by_contra hxy
    obtain ⟨ψ, hψ⟩ := exists_pontryaginDual_apply_ne_one (div_ne_one.mpr hxy)
    exact hψ (by rw [map_div, show ψ x = ψ y from congrFun h ψ, div_self'])
  let L := ev.range.topologicalClosure
  let : CompactSpace L := isCompact_iff_compactSpace.mp ev.range.isClosed_topologicalClosure.isCompact
  let j : G →ₜ* L :=
    ⟨ev.codRestrict L (fun x ↦ ev.range.le_topologicalClosure ⟨x, rfl⟩), hev.subtype_mk _⟩
  have hj : Function.Injective j := fun _ _ h ↦ hinj (congrArg Subtype.val h)
  obtain ⟨ψ, hψ⟩ := exists_pontryaginDual_extension_of_compact (j.comp i) (hj.comp hi) χ
  exact ⟨ψ.comp j, hψ⟩

omit [T2Space G] in
/-- A character of a closed subgroup which is trivial on its intersection with a compact
subgroup extends to a character trivial on the whole compact subgroup. In the quotient of
`G × Circle` by the graph and the compact subgroup, the circle factor still embeds. -/
theorem exists_pontryaginDual_extension_trivial_on_compact (H K : Subgroup G)
    (hH : IsClosed (H : Set G)) (hK : IsCompact (K : Set G))
    (χ : PontryaginDual H) (hχ : ∀ x : H, (x : G) ∈ K → χ x = 1) :
    ∃ ψ : PontryaginDual G, (∀ x : H, ψ x = χ x) ∧ ∀ x : K, ψ x = 1 := by
  -- Quotient by the graph of χ and by the compact subgroup where the extension must vanish.
  let graph := (H.subtype.prod χ.toMonoidHom).range
  let K₀ := K.prod (⊥ : Subgroup Circle)
  let D := graph ⊔ K₀
  have hGraph : IsClosed (graph : Set (G × Circle)) := by
    rw [MonoidHom.coe_range]
    let f : H × Circle → G × Circle := Prod.map Subtype.val id
    have hf : IsClosedEmbedding f := hH.isClosedEmbedding_subtypeVal.prodMap IsClosedEmbedding.id
    have hc : IsClosed {p : H × Circle | χ p.1 = p.2} :=
      isClosed_eq (χ.continuous.comp continuous_fst) continuous_snd
    convert hf.isClosedMap _ hc using 1
    ext p
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨(x, χ x), rfl, rfl⟩
    · rintro ⟨⟨x, z⟩, hz, rfl⟩
      exact ⟨x, Prod.ext rfl hz⟩
  have hK₀ : IsCompact (K₀ : Set (G × Circle)) := by
    simpa [K₀, Subgroup.coe_prod] using hK.prod (isCompact_singleton (x := (1 : Circle)))
  let : IsClosed (D : Set (G × Circle)) := by
    rw [Subgroup.mul_normal]
    exact hGraph.mul_right_of_isCompact hK₀
  let q : G × Circle →ₜ* (G × Circle) ⧸ D :=
    ⟨QuotientGroup.mk' D, QuotientGroup.continuous_mk⟩
  let i : Circle →ₜ* (G × Circle) ⧸ D :=
    q.comp ⟨MonoidHom.inr G Circle, continuous_const.prodMk continuous_id⟩
  have hInj : Function.Injective i := by
    apply (injective_iff_map_eq_one i.toMonoidHom).mpr
    intro z hz
    obtain ⟨_, ⟨x, rfl⟩, ⟨k, w⟩, ⟨hk, hw⟩, he⟩ :=
      Subgroup.mem_sup.mp ((QuotientGroup.eq_one_iff (1, z)).mp hz)
    have hx : (x : G) * k = 1 := congrArg Prod.fst he
    have hw' : w = 1 := Subgroup.mem_bot.mp hw
    have hxK : (x : G) ∈ K :=
      (eq_inv_of_mul_eq_one_left hx).symm ▸ K.inv_mem hk
    have hz' : χ x * w = z := congrArg Prod.snd he
    simpa [hχ x hxK, hw'] using hz'.symm
  let idχ : PontryaginDual Circle := ContinuousMonoidHom.id Circle
  obtain ⟨ψ, hψ⟩ := exists_extension_of_compact_source i hInj idχ
  let Ψ := ψ.comp q
  let ψG : PontryaginDual G :=
    (Ψ.comp ⟨MonoidHom.inl G Circle, continuous_id.prodMk continuous_const⟩)⁻¹
  have hTrivial (p : G × Circle) (hp : p ∈ D) : Ψ p = 1 := by
    change ψ (q p) = 1
    rw [show q p = 1 from (QuotientGroup.eq_one_iff p).mpr hp, map_one]
  refine ⟨ψG, fun x ↦ ?_, fun x ↦ ?_⟩
  · have hGraphMem : (↑x, χ x) ∈ graph := ⟨x, rfl⟩
    have h := hTrivial (x, χ x) ((show graph ≤ D from le_sup_left) hGraphMem)
    rw [show ((x : G), χ x) = ((x : G), 1) * (1, χ x) by simp, map_mul] at h
    change (Ψ (x, 1))⁻¹ = χ x
    exact (eq_inv_of_mul_eq_one_right (show Ψ (x, 1) * χ x = 1 from
      (hψ (χ x)) ▸ h)).symm
  · have hCompactMem : (↑x, 1) ∈ K₀ := ⟨x.property, Subgroup.one_mem _⟩
    have h := hTrivial (x, 1) ((show K₀ ≤ D from le_sup_right) hCompactMem)
    change (Ψ (x, 1))⁻¹ = 1
    simp [h]

end Restriction

/-! ### Compact polars in the dual -/

/-- There is a radius such that characters mapping any fixed identity neighborhood into
the closed circle ball of that radius form a compact set in the compact-open topology.
Powers give equicontinuity at the identity, and Arzelà–Ascoli gives compactness. -/
theorem exists_isCompact_pontryaginDual_polar {G : Type*} [CommGroup G]
    [TopologicalSpace G] [IsTopologicalGroup G] :
    ∃ r : ℝ, 0 < r ∧ ∀ U ∈ 𝓝 (1 : G),
      IsCompact {χ : PontryaginDual G | MapsTo χ U (Metric.closedBall 1 r)} := by
  classical
  have hArc : Circle.centeredArc (Real.pi / 2) ∈ 𝓝 (1 : Circle) := by
    simpa using Circle.hasBasis_centeredArc_div_two_pow.mem_of_mem (i := 0) trivial
  obtain ⟨r, hr, hBall⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hArc
  refine ⟨r, hr, fun U hU ↦ ?_⟩
  let W := Metric.closedBall (1 : Circle) r
  let S := {f : G →* Circle | MapsTo f U W}
  have hEqui : Equicontinuous (fun f : S ↦ (f.1 : G → Circle)) := by
    refine equicontinuous_of_equicontinuousAt_one Subtype.val ?_
    apply (Metric.equicontinuousAt_iff_right (α := Circle)).mpr
    intro ε hε
    let T (n : ℕ) := (fun z : Circle ↦ z ^ n) ⁻¹' W
    have hDisj : Disjoint (Metric.ball (1 : Circle) ε)ᶜ (⋂ n, T n) := by
      refine Set.disjoint_left.mpr fun z hz hzT ↦ ?_
      have hz1 := Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two (z := z)
        (fun n _ ↦ hBall (mem_iInter.mp hzT n))
      exact hz (hz1.symm ▸ Metric.mem_ball_self hε)
    obtain ⟨N, hN⟩ := (isClosed_compl_iff.mpr Metric.isOpen_ball).isCompact
      |>.elim_finite_subfamily_closed T
        (fun n ↦ Metric.isClosed_closedBall.preimage (continuous_pow n))
        (Set.disjoint_iff_inter_eq_empty.mp hDisj)
    replace hN : Disjoint (Metric.ball (1 : Circle) ε)ᶜ (⋂ n ∈ N, T n) :=
      Set.disjoint_iff_inter_eq_empty.mpr hN
    have hNear : ∀ᶠ x : G in 𝓝 1, ∀ n ∈ N, x ^ n ∈ U :=
      (eventually_all_finset N).2 fun n _ ↦
        (continuous_pow n).tendsto' 1 1 (one_pow n) hU
    filter_upwards [hNear] with x hx f
    have hPow : f.1 x ∈ ⋂ n ∈ N, T n := by
      simp only [mem_iInter, T, mem_preimage, ← map_pow]
      exact fun n hn ↦ f.2 (hx n hn)
    have hMem : f.1 x ∈ Metric.ball (1 : Circle) ε := by
      by_contra hz
      exact (Set.disjoint_left.mp hN) hz hPow
    simpa [Function.comp_def, map_one, Metric.mem_ball, dist_comm] using hMem
  let A := {f : ContinuousMonoidHom G Circle | MapsTo f U W}
  let C := ContinuousMonoidHom.toContinuousMap '' A
  have hPointwise : ContinuousMap.toFun '' C =
      Set.pi U (fun _ ↦ W) ∩ Set.range ((⇑) : (G →* Circle) → G → Circle) := by
    ext f
    constructor
    · rintro ⟨_, ⟨ψ, hψ, rfl⟩, rfl⟩
      exact ⟨hψ, ψ.toMonoidHom, rfl⟩
    · rintro ⟨hf, ψ, rfl⟩
      let ψc : ContinuousMonoidHom G Circle :=
        { toMonoidHom := ψ, continuous_toFun := hEqui.continuous ⟨ψ, hf⟩ }
      exact ⟨ψc.toContinuousMap, ⟨ψc, hf, rfl⟩, rfl⟩
  have hC : IsCompact C := by
    apply ArzelaAscoli.isCompact_of_equicontinuous
    · rw [hPointwise]
      exact ((isClosed_set_pi fun _ _ ↦ Metric.isClosed_closedBall).inter
        (MonoidHom.isClosed_range_coe G Circle)).isCompact
    · refine (equicontinuous_iff_range (F := fun f : C ↦ f.1.toFun)).mpr ?_
      rw [← Set.image_eq_range ContinuousMap.toFun C, hPointwise]
      have hRange : range (fun f : S ↦ (f.1 : G → Circle)) =
          Set.pi U (fun _ ↦ W) ∩ Set.range ((⇑) : (G →* Circle) → G → Circle) := by
        ext f
        constructor
        · rintro ⟨ψ, rfl⟩
          exact ⟨ψ.2, ψ.1, rfl⟩
        · rintro ⟨hf, ψ, rfl⟩
          exact ⟨⟨ψ, hf⟩, rfl⟩
      rw [← hRange]
      exact equicontinuous_iff_range.mp hEqui
  exact (ContinuousMonoidHom.isInducing_toContinuousMap G Circle).isCompact_iff.mpr hC

/-! ### The restriction map is open -/

section Open

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]

/-- The annihilator of `H` is the kernel of the restriction map `Ĝ → Ĥ`. -/
theorem coe_annihilator_eq_preimage {G : Type*} [CommGroup G] [TopologicalSpace G]
    (H : Subgroup G) :
    (LCAGroup.annihilator H : Set (PontryaginDual G)) =
      (PontryaginDual.map (⟨H.subtype, continuous_subtype_val⟩ : H →ₜ* G)) ⁻¹' {1} := by
  ext χ
  constructor
  · intro h
    exact PontryaginDual.ext fun x ↦ h x x.2
  · intro h x hx
    exact congrArg (fun ψ : PontryaginDual H ↦ ψ ⟨x, hx⟩) h

/-- Some compact subgroup has a σ-compact annihilator. The subgroup is the
intersection of a decreasing sequence of compact identity neighborhoods. -/
theorem exists_compact_subgroup_sigmaCompact_annihilator :
    ∃ K : Subgroup G, IsCompact (K : Set G) ∧ SigmaCompactSpace (LCAGroup.annihilator K) := by
  let N := {U : Set G // U ∈ 𝓝 (1 : G) ∧ IsCompact U}
  have hNext (U : N) : ∃ V : N, (V : Set G)⁻¹ = V.val ∧ V.val * V.val ⊆ U.val := by
    obtain ⟨V, hV, hVc, hVi, hVV⟩ := exists_closed_nhds_one_inv_eq_mul_subset U.property.1
    have hVU : V ⊆ U.val := fun x hx ↦ hVV (mul_one x ▸ Set.mul_mem_mul hx (mem_of_mem_nhds hV))
    exact ⟨⟨V, hV, U.property.2.of_isClosed_subset hVc hVU⟩, hVi, hVV⟩
  choose next hInv hMul using hNext
  obtain ⟨U₀, hU₀, hU₀nhds⟩ := exists_compact_mem_nhds (1 : G)
  let seq : ℕ → N := Nat.rec ⟨U₀, hU₀nhds, hU₀⟩ fun _ U ↦ next U
  let U (n : ℕ) : Set G := (seq n).val
  have hOne (n : ℕ) : (1 : G) ∈ U n := mem_of_mem_nhds (seq n).property.1
  have hMulU (n : ℕ) : U (n + 1) * U (n + 1) ⊆ U n := hMul (seq n)
  have hAnti : Antitone U := antitone_nat_of_succ_le fun n x hx ↦
    hMulU n (mul_one x ▸ Set.mul_mem_mul hx (hOne (n + 1)))
  let K : Subgroup G :=
    { carrier := ⋂ n, U n
      one_mem' := mem_iInter.mpr hOne
      mul_mem' := fun hx hy ↦ mem_iInter.mpr fun n ↦ hMulU n
        (Set.mul_mem_mul (mem_iInter.mp hx (n + 1)) (mem_iInter.mp hy (n + 1)))
      inv_mem' := fun hx ↦ mem_iInter.mpr fun n ↦ hAnti (Nat.le_succ n) (by
          change _ ∈ (next (seq n)).val
          rw [← hInv (seq n)]
          simpa only [Set.mem_inv, inv_inv] using mem_iInter.mp hx (n + 1)) }
  have hUc (n) : IsCompact (U n) := (seq n).property.2
  have hUK : IsClosed (K : Set G) := isClosed_iInter fun n ↦ (hUc n).isClosed
  have hK : IsCompact (K : Set G) := (hUc 0).of_isClosed_subset hUK (iInter_subset U 0)
  refine ⟨K, hK, ?_⟩
  obtain ⟨r, hr, hPolar⟩ := exists_isCompact_pontryaginDual_polar (G := G)
  let A := LCAGroup.annihilator K
  have hA : IsClosed (A : Set (PontryaginDual G)) := by
    rw [coe_annihilator_eq_preimage]
    exact isClosed_singleton.preimage
      (PontryaginDual.map (⟨K.subtype, continuous_subtype_val⟩ : K →ₜ* G)).continuous
  let P (n : ℕ) : Set A := Subtype.val ⁻¹' {χ | MapsTo χ (U n) (Metric.closedBall 1 r)}
  refine ⟨⟨P, fun n ↦ (?_ : IsCompact (P n)), eq_univ_of_forall fun χ ↦ ?_⟩⟩
  · exact hA.isClosedEmbedding_subtypeVal.isCompact_preimage (hPolar _ (seq n).property.1)
  · let W := (χ.val : PontryaginDual G) ⁻¹' Metric.ball 1 r
    have hW : IsOpen W := Metric.isOpen_ball.preimage χ.val.continuous
    have hKW : (K : Set G) ⊆ W := fun x hx ↦
      show χ.val x ∈ Metric.ball 1 r by
        rw [(LCAGroup.mem_annihilator_iff K χ.val).mp χ.property x hx]
        exact Metric.mem_ball_self hr
    have hDisj : Disjoint (U 0 \ W) (⋂ n, U n) :=
      Set.disjoint_left.mpr fun x hx hxn ↦ hx.2 (hKW hxn)
    obtain ⟨n, hn⟩ := ((hUc 0).diff hW).elim_directed_family_closed U
      (fun n ↦ (hUc n).isClosed) (Set.disjoint_iff_inter_eq_empty.mp hDisj) hAnti.directed_ge
    replace hn : Disjoint (U 0 \ W) (U n) := Set.disjoint_iff_inter_eq_empty.mpr hn
    refine mem_iUnion.mpr ⟨n, fun x hx ↦ Metric.ball_subset_closedBall ?_⟩
    by_contra hxW
    exact Set.disjoint_left.mp hn ⟨hAnti (Nat.zero_le n) hx, hxW⟩ hx

/-- Restriction to a closed subgroup is an open map on the dual groups. -/
theorem isOpenMap_restrict_dual (H : Subgroup G) (hH : IsClosed (H : Set G)) :
    IsOpenMap (PontryaginDual.map (⟨H.subtype, continuous_subtype_val⟩ : H →ₜ* G)) := by
  let f := PontryaginDual.map (⟨H.subtype, continuous_subtype_val⟩ : H →ₜ* G)
  let : LocallyCompactSpace H := hH.locallyCompactSpace
  obtain ⟨K, hK, hSigma⟩ := exists_compact_subgroup_sigmaCompact_annihilator (G := G)
  -- The restriction between the two open annihilators is surjective.
  let L := K.comap H.subtype
  have hL : IsCompact (L : Set H) := hH.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  let A := LCAGroup.annihilator K
  let B := LCAGroup.annihilator L
  let : SigmaCompactSpace A := hSigma
  let : CompactSpace L := isCompact_iff_compactSpace.mp hL
  have hB : IsOpen (B : Set (PontryaginDual H)) := by
    rw [coe_annihilator_eq_preimage]
    exact (isOpen_discrete ({1} : Set (PontryaginDual L))).preimage
      (PontryaginDual.map (⟨L.subtype, continuous_subtype_val⟩ : L →ₜ* H)).continuous
  let : LocallyCompactSpace B := hB.isOpenEmbedding_subtypeVal.locallyCompactSpace
  let g : A →* B := (f.toMonoidHom.comp A.subtype).codRestrict B fun χ ↦
    (LCAGroup.mem_annihilator_iff L _).mpr fun x hx ↦
      (LCAGroup.mem_annihilator_iff K χ.val).mp χ.property (x : G) hx
  have hg : Continuous g := (f.continuous.comp continuous_subtype_val).subtype_mk _
  have hgSurj : Function.Surjective g := by
    intro χ
    obtain ⟨ψ, hψ, hψK⟩ := exists_pontryaginDual_extension_trivial_on_compact H K hH hK χ.val
      (fun x hx ↦ (LCAGroup.mem_annihilator_iff L χ.val).mp χ.property x hx)
    exact ⟨⟨ψ, (LCAGroup.mem_annihilator_iff K ψ).mpr fun x hx ↦ hψK ⟨x, hx⟩⟩,
      Subtype.ext (PontryaginDual.ext hψ)⟩
  have hOpen := g.isOpenMap_of_sigmaCompact hgSurj hg
  have hImg (U : Set (PontryaginDual G)) (hU : U ∈ 𝓝 1) : f '' U ∈ 𝓝 1 := by
    have hU' : (Subtype.val : A → PontryaginDual G) ⁻¹' U ∈ 𝓝 (1 : A) :=
      continuous_subtype_val.continuousAt.preimage_mem_nhds hU
    have hV := hOpen.image_mem_nhds hU'
    rw [map_one g] at hV
    apply mem_of_superset (hB.isOpenEmbedding_subtypeVal.isOpenMap.image_mem_nhds hV)
    rintro _ ⟨_, ⟨χ, hχ, rfl⟩, rfl⟩
    exact ⟨χ.val, hχ, rfl⟩
  exact IsTopologicalGroup.isOpenMap_iff_nhds_one.mpr fun U hU ↦
    mem_of_superset (hImg (f ⁻¹' U) hU) (image_preimage_subset f U)

end Open

end Sol_LCAGroup_dual_quotient_annihilator_equiv_dual_subgroup

open LCAGroup Sol_LCAGroup_dual_quotient_annihilator_equiv_dual_subgroup in
theorem solution
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G)) :
    ∃ e : (PontryaginDual G ⧸ annihilator H) ≃ₜ* PontryaginDual H,
      ∀ (χ : PontryaginDual G) (x : H),
        e (χ : PontryaginDual G ⧸ annihilator H) x = χ (x : G) := by
  let f := PontryaginDual.map (⟨H.subtype, continuous_subtype_val⟩ : H →ₜ* G)
  have hSurj : Function.Surjective f := by
    intro χ
    obtain ⟨ψ, hψ, _⟩ := exists_pontryaginDual_extension_trivial_on_compact H ⊥ hH
      (by simp) χ (fun x hx ↦ by
        have hx1 : x = 1 := Subtype.ext (Subgroup.mem_bot.mp hx)
        rw [hx1, map_one])
    exact ⟨ψ, PontryaginDual.ext hψ⟩
  have hOpen := isOpenMap_restrict_dual H hH
  have hker : annihilator H = f.toMonoidHom.ker := by
    ext χ
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      exact PontryaginDual.ext fun x ↦ h x x.2
    · intro h x hx
      exact congrArg (fun ψ : PontryaginDual H ↦ ψ ⟨x, hx⟩) h
  let e := (QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivOfSurjective f.toMonoidHom hSurj)
  have hq := QuotientGroup.isQuotientMap_mk (annihilator H)
  have hf := hOpen.isQuotientMap f.continuous hSurj
  refine ⟨e.toContinuousMulEquiv fun _ ↦ ?_, fun _ _ ↦ rfl⟩
  exact (hq.isCoinducing.isOpen_preimage.symm.trans hf.isCoinducing.isOpen_preimage)
