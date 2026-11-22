-- Prove2me | solution 1 for MasulloGRH.normOneIdeleClassGroup_connectedComponentOfOne_equiv
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T20:08:47.970808+00:00
-- url     : https://prove2.me/submissions/4d30d615-55ce-4d44-b39d-cd0f15ba76ef
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MasulloGRH_IdeleNorm
import Theorems.Thm_MasulloGRH_idele_class_group_topology
import Theorems.Thm_MasulloGRH_s_idele_class_group_open_embedding
import Theorems.Thm_MasulloGRH_closure_image_connectedComponentOfOne_normOneIdeles_equiv

open NumberField

set_option autoImplicit false

namespace Sol_MasulloGRH_normOneIdeleClassGroup_connectedComponentOfOne_equiv

open MasulloGRH IsDedekindDomain

variable {F : Type*} [Field F] [NumberField F]

lemma fin_mul_apply (g h : IdeleGroup F) (v : HeightOneSpectrum (𝓞 F)) :
    ((g * h : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v =
      (g : AdeleRing (𝓞 F) F).2 v * (h : AdeleRing (𝓞 F) F).2 v := rfl

lemma inf_mul_apply (g h : IdeleGroup F) (w : InfinitePlace F) :
    ((g * h : IdeleGroup F) : AdeleRing (𝓞 F) F).1 w =
      (g : AdeleRing (𝓞 F) F).1 w * (h : AdeleRing (𝓞 F) F).1 w := rfl

lemma fin_one_apply (v : HeightOneSpectrum (𝓞 F)) :
    ((1 : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v = 1 := rfl

lemma inf_one_apply (w : InfinitePlace F) :
    ((1 : IdeleGroup F) : AdeleRing (𝓞 F) F).1 w = 1 := rfl

/-- The finite-part norms of an idele are `1` at almost all places. -/
lemma mulSupport_finite (g : IdeleGroup F) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      ‖(g : AdeleRing (𝓞 F) F).2 v‖).Finite := by
  have hx := ((g : AdeleRing (𝓞 F) F).2).eventually
  have hy := (((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2).eventually
  have hxy : ∀ v, (g : AdeleRing (𝓞 F) F).2 v *
      ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v = 1 := by
    intro v
    rw [← fin_mul_apply, mul_inv_cancel, fin_one_apply]
  have hev : ∀ᶠ v in Filter.cofinite, ‖(g : AdeleRing (𝓞 F) F).2 v‖ = 1 := by
    filter_upwards [hx, hy] with v h1 h2
    have n1 : ‖(g : AdeleRing (𝓞 F) F).2 v‖ ≤ 1 :=
      (Valued.toNormedField.norm_le_one_iff).2 h1
    have n2 : ‖((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v‖ ≤ 1 :=
      (Valued.toNormedField.norm_le_one_iff).2 h2
    have n3 : ‖(g : AdeleRing (𝓞 F) F).2 v‖ *
        ‖((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v‖ = 1 := by
      rw [← norm_mul, hxy v, norm_one]
    nlinarith [norm_nonneg ((g : AdeleRing (𝓞 F) F).2 v),
      norm_nonneg (((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v)]
  exact Filter.eventually_cofinite.1 hev

lemma ideleNorm_mul' (g h : IdeleGroup F) :
    ideleNorm (g * h) = ideleNorm g * ideleNorm h := by
  unfold ideleNorm
  have e1 : ∀ w : InfinitePlace F,
      ‖((g * h : IdeleGroup F) : AdeleRing (𝓞 F) F).1 w‖ ^ w.mult =
        ‖(g : AdeleRing (𝓞 F) F).1 w‖ ^ w.mult * ‖(h : AdeleRing (𝓞 F) F).1 w‖ ^ w.mult := by
    intro w
    rw [inf_mul_apply, norm_mul, mul_pow]
  have e2 : ∀ v : HeightOneSpectrum (𝓞 F),
      ‖((g * h : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v‖ =
        ‖(g : AdeleRing (𝓞 F) F).2 v‖ * ‖(h : AdeleRing (𝓞 F) F).2 v‖ := by
    intro v
    rw [fin_mul_apply, norm_mul]
  simp_rw [e1, e2, Finset.prod_mul_distrib]
  rw [finprod_mul_distrib (mulSupport_finite g) (mulSupport_finite h)]
  ring

lemma ideleNorm_one' : ideleNorm (1 : IdeleGroup F) = 1 := by
  unfold ideleNorm
  simp_rw [inf_one_apply, fin_one_apply, norm_one, one_pow, Finset.prod_const_one, finprod_one,
    one_mul]

/-- The idelic norm as a monoid homomorphism `GL₁(𝔸_F) → ℝ`. -/
noncomputable def normHom (F : Type*) [Field F] [NumberField F] : IdeleGroup F →* ℝ where
  toFun := ideleNorm
  map_one' := ideleNorm_one'
  map_mul' := ideleNorm_mul'

lemma normHom_apply (g : IdeleGroup F) : normHom F g = ideleNorm g := rfl

lemma finite_norm_eq_one_of_mem {g : IdeleGroup F}
    (hg : g ∈ sIntegralIdeles (∅ : Finset (HeightOneSpectrum (𝓞 F))))
    (v : HeightOneSpectrum (𝓞 F)) : ‖(g : AdeleRing (𝓞 F) F).2 v‖ = 1 := by
  have h := hg v (Finset.notMem_empty v)
  apply le_antisymm
  · exact (Valued.toNormedField.norm_le_one_iff).2 h.le
  · exact (Valued.toNormedField.one_le_norm_iff).2 h.ge

lemma continuous_ideleNorm : Continuous (ideleNorm : IdeleGroup F → ℝ) := by
  obtain ⟨U, hU, hUo, -⟩ := s_idele_class_group_open_embedding F ∅
  let f : IdeleGroup F → ℝ := fun g => ∏ w : InfinitePlace F, ‖(g : AdeleRing (𝓞 F) F).1 w‖ ^ w.mult
  have hf : Continuous f := by
    have h0 : Continuous (fun g : IdeleGroup F => (g : AdeleRing (𝓞 F) F).1) :=
      continuous_fst.comp (Units.continuous_val (M := AdeleRing (𝓞 F) F))
    have h1 : ∀ w : InfinitePlace F, Continuous (fun x : InfiniteAdeleRing F => x w) :=
      fun w => continuous_apply w
    refine continuous_finsetProd _ (fun w _ => ?_)
    exact (continuous_norm.comp ((h1 w).comp h0)).pow _
  have h1 : (1 : IdeleGroup F) ∈ (U : Set (IdeleGroup F)) := U.one_mem
  have heq : f =ᶠ[nhds (1 : IdeleGroup F)] (normHom F) := by
    filter_upwards [hUo.mem_nhds h1] with g hg
    rw [hU] at hg
    rw [normHom_apply]
    unfold ideleNorm
    have : (∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(g : AdeleRing (𝓞 F) F).2 v‖) = 1 := by
      rw [finprod_congr (finite_norm_eq_one_of_mem hg), finprod_one]
    rw [this, mul_one]
  have hc : ContinuousAt (normHom F) 1 := hf.continuousAt.congr heq
  exact continuous_of_continuousAt_one (normHom F) hc

lemma principal_le_ker : principalIdeles F ≤ (normHom F).ker := by
  rintro x ⟨ξ, rfl⟩
  rw [MonoidHom.mem_ker, normHom_apply]
  exact (idele_class_group_topology F).2.2.2.2.1 ξ

/-- The idelic norm on the idele class group. -/
noncomputable def classNorm (F : Type*) [Field F] [NumberField F] : IdeleClassGroup F →* ℝ :=
  QuotientGroup.lift (principalIdeles F) (normHom F) principal_le_ker

lemma classNorm_mk (g : IdeleGroup F) :
    classNorm F (QuotientGroup.mk g : IdeleClassGroup F) = ideleNorm g := rfl

lemma continuous_classNorm : Continuous (classNorm F) :=
  (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 continuous_ideleNorm

lemma cc_le_closure {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (K L : Subgroup G)
    (h : ∀ W ∈ nhds (1 : G), ∃ O : Subgroup G, L ≤ O ∧ O ≤ K ∧
       IsOpen ((O.subgroupOf K : Subgroup K) : Set K) ∧
       ∀ o ∈ O, ∃ l ∈ L, ∃ w ∈ W, o = l * w) :
    (Subgroup.connectedComponentOfOne K).map K.subtype ≤ L.topologicalClosure := by
  rintro _ ⟨x, hx, rfl⟩
  show (x : G) ∈ closure (L : Set G)
  rw [mem_closure_iff_nhds]
  intro N hN
  have hW : (fun w : G => (x : G) * w⁻¹) ⁻¹' N ∈ nhds (1 : G) := by
    have hc : ContinuousAt (fun w : G => (x : G) * w⁻¹) 1 :=
      (continuous_const.mul continuous_inv).continuousAt
    apply hc.preimage_mem_nhds
    simpa using hN
  obtain ⟨O, -, -, hOo, hOW⟩ := h _ hW
  have hclopen : IsClopen ((O.subgroupOf K : Subgroup K) : Set K) :=
    ⟨Subgroup.isClosed_of_isOpen _ hOo, hOo⟩
  have hsub := hclopen.connectedComponent_subset (x := (1 : K)) (Subgroup.one_mem _)
  have hxO : (x : G) ∈ O := hsub hx
  obtain ⟨l, hl, w, hw, hlw⟩ := hOW _ hxO
  refine ⟨l, ?_, hl⟩
  have : l = (x : G) * w⁻¹ := by rw [hlw]; group
  rw [this]; exact hw

/-- The archimedean ideles inside the ideles. -/
noncomputable def iInf : (InfiniteAdeleRing F)ˣ →* IdeleGroup F :=
  (MulEquiv.prodUnits (M := InfiniteAdeleRing F) (N := FiniteAdeleRing (𝓞 F) F)).symm.toMonoidHom.comp
    (MonoidHom.inl _ _)

/-- The finite ideles inside the ideles. -/
noncomputable def iFin : (FiniteAdeleRing (𝓞 F) F)ˣ →* IdeleGroup F :=
  (MulEquiv.prodUnits (M := InfiniteAdeleRing F) (N := FiniteAdeleRing (𝓞 F) F)).symm.toMonoidHom.comp
    (MonoidHom.inr _ _)

lemma continuous_iInf : Continuous (iInf (F := F)) :=
  (Homeomorph.prodUnits (α := InfiniteAdeleRing F) (β := FiniteAdeleRing (𝓞 F) F)).symm.continuous.comp
    (continuous_id.prodMk continuous_const)

lemma continuous_iFin : Continuous (iFin (F := F)) :=
  (Homeomorph.prodUnits (α := InfiniteAdeleRing F) (β := FiniteAdeleRing (𝓞 F) F)).symm.continuous.comp
    (continuous_const.prodMk continuous_id)

/-- The splitting map. -/
noncomputable def split : IdeleGroup F ≃ₜ (InfiniteAdeleRing F)ˣ × (FiniteAdeleRing (𝓞 F) F)ˣ :=
  Homeomorph.prodUnits (α := InfiniteAdeleRing F) (β := FiniteAdeleRing (𝓞 F) F)

lemma split_apply (g : IdeleGroup F) :
    split g = MulEquiv.prodUnits (M := InfiniteAdeleRing F) (N := FiniteAdeleRing (𝓞 F) F) g := rfl

lemma eq_iInf_mul_iFin (g : IdeleGroup F) : g = iInf (split g).1 * iFin (split g).2 := by
  set e := MulEquiv.prodUnits (M := InfiniteAdeleRing F) (N := FiniteAdeleRing (𝓞 F) F)
  have h1 : g = e.symm (e g) := (e.symm_apply_apply g).symm
  have h2 : e g = ((e g).1, 1) * (1, (e g).2) := by
    ext <;> simp
  rw [split_apply]
  conv_lhs => rw [h1, h2, map_mul]
  rfl

lemma ideleNorm_iInf (a : (InfiniteAdeleRing F)ˣ) :
    ideleNorm (iInf a) = ∏ w : InfinitePlace F, ‖(a : InfiniteAdeleRing F) w‖ ^ w.mult := by
  have h1 : ∀ w, ((iInf a : IdeleGroup F) : AdeleRing (𝓞 F) F).1 w = (a : InfiniteAdeleRing F) w :=
    fun w => rfl
  have h2 : ∀ v, ((iInf a : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v = 1 := fun v => rfl
  unfold ideleNorm
  simp_rw [h1, h2, norm_one, finprod_one, mul_one]

lemma ideleNorm_iFin (u : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (hu : ∀ v : HeightOneSpectrum (𝓞 F), ‖(u : FiniteAdeleRing (𝓞 F) F) v‖ = 1) :
    ideleNorm (iFin u) = 1 := by
  have h1 : ∀ w, ((iFin u : IdeleGroup F) : AdeleRing (𝓞 F) F).1 w = 1 := fun w => rfl
  have h2 : ∀ v, ((iFin u : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v = (u : FiniteAdeleRing (𝓞 F) F) v :=
    fun v => rfl
  unfold ideleNorm
  simp_rw [h1, h2, hu, norm_one, one_pow, Finset.prod_const_one, finprod_one, mul_one]

/-- Neighbourhoods of `1` in a topological monoid of units. -/
lemma units_nhds_one {M : Type*} [Monoid M] [TopologicalSpace M] (V : Set Mˣ) (hV : V ∈ nhds 1) :
    ∃ N ∈ nhds (1 : M), ∀ u : Mˣ, (u : M) ∈ N → ((u⁻¹ : Mˣ) : M) ∈ N → u ∈ V := by
  rw [Units.isInducing_embedProduct.nhds_eq_comap] at hV
  obtain ⟨t, ht, htV⟩ := Filter.mem_comap.1 hV
  have ht' : t ∈ nhds (1 : M) ×ˢ nhds (MulOpposite.op (1 : M)) := by
    rw [← nhds_prod_eq]; simpa using ht
  obtain ⟨t1, ht1, t2, ht2, hsub⟩ := Filter.mem_prod_iff.1 ht'
  have ht2' : MulOpposite.op ⁻¹' t2 ∈ nhds (1 : M) :=
    MulOpposite.continuous_op.continuousAt.preimage_mem_nhds ht2
  refine ⟨t1 ∩ MulOpposite.op ⁻¹' t2, Filter.inter_mem ht1 ht2', fun u h1 h2 => htV ?_⟩
  exact hsub ⟨h1.1, h2.2⟩

/-- Neighbourhoods of `1` in the finite adeles, in restricted-product form. -/
lemma rp_nhds_one
    (N : Set (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
        (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite))
    (hN : N ∈ nhds 1) :
    ∃ I : Set (HeightOneSpectrum (𝓞 F)), I.Finite ∧ ∃ ε : HeightOneSpectrum (𝓞 F) → ℝ,
      (∀ v, 0 < ε v) ∧ ∀ x : RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
        (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite,
        (∀ v, ‖x v - 1‖ ≤ 1) → (∀ v ∈ I, ‖x v - 1‖ < ε v) → x ∈ N := by
  classical
  have hopen : ∀ v : HeightOneSpectrum (𝓞 F),
      IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    fun v => Valued.isOpen_valuationSubring _
  have : Fact (∀ v : HeightOneSpectrum (𝓞 F),
      IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F))) := ⟨hopen⟩
  have hN0 : (fun x => x + 1) ⁻¹' N ∈ nhds 0 := by
    apply (continuous_add_const _).continuousAt.preimage_mem_nhds
    simpa using hN
  let x0 : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletionIntegers F := 0
  have key := RestrictedProduct.nhds_eq_map_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) hopen x0
  have h3 : (fun x => x + 1) ⁻¹' N ∈ nhds (RestrictedProduct.structureMap
    (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite x0) := hN0
  rw [key, Filter.mem_map, nhds_pi, Filter.mem_pi] at h3
  obtain ⟨I, hI, t, ht, hIt⟩ := h3
  have hε : ∀ v : HeightOneSpectrum (𝓞 F), ∃ ε > 0, ∀ x : v.adicCompletionIntegers F,
      ‖(x : v.adicCompletion F)‖ < ε → x ∈ t v := by
    intro v
    obtain ⟨ε, hε0, hεt⟩ := Metric.mem_nhds_iff.1 (ht v)
    refine ⟨ε, hε0, fun x hx => hεt ?_⟩
    rw [Metric.mem_ball, Subtype.dist_eq,
      show ((x0 v : v.adicCompletionIntegers F) : v.adicCompletion F) = 0 from rfl, dist_zero_right]
    exact hx
  choose ε hε0 hεt using hε
  refine ⟨I, hI, ε, hε0, fun x hx1 hxI => ?_⟩
  let y : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletionIntegers F := fun v =>
    ⟨x v - 1, (Valued.toNormedField.norm_le_one_iff).1 (hx1 v)⟩
  have hy : y ∈ I.pi t := fun v hv => hεt v (y v) (hxI v hv)
  have h4 := hIt hy
  have h5 : RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => v.adicCompletionIntegers F) Filter.cofinite y + 1 = x := by
    apply Subtype.ext
    funext v
    show (x v - 1) + 1 = x v
    ring
  have h6 : RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => v.adicCompletionIntegers F) Filter.cofinite y + 1 ∈ N := h4
  rwa [h5] at h6

/-- (R1) small open subgroups of the finite unit ideles. -/
lemma exists_openSubgroup (V : Set (FiniteAdeleRing (𝓞 F) F)ˣ) (hV : V ∈ nhds 1) :
    ∃ U : Subgroup (FiniteAdeleRing (𝓞 F) F)ˣ, IsOpen (U : Set (FiniteAdeleRing (𝓞 F) F)ˣ) ∧
      (∀ u ∈ U, ∀ v : HeightOneSpectrum (𝓞 F), ‖(u : FiniteAdeleRing (𝓞 F) F) v‖ = 1) ∧
      (U : Set (FiniteAdeleRing (𝓞 F) F)ˣ) ⊆ V := by
  classical
  obtain ⟨N, hN, hNV⟩ := units_nhds_one V hV
  obtain ⟨I, hI, ε, hε0, hεN⟩ := rp_nhds_one (F := F) N hN
  have hmul : ∀ (u w : (FiniteAdeleRing (𝓞 F) F)ˣ) (v : HeightOneSpectrum (𝓞 F)),
      ((u * w : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v =
        (u : FiniteAdeleRing (𝓞 F) F) v * (w : FiniteAdeleRing (𝓞 F) F) v := fun u w v => rfl
  have hone : ∀ v : HeightOneSpectrum (𝓞 F),
      ((1 : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v = 1 := fun v => rfl
  have hinv : ∀ (u : (FiniteAdeleRing (𝓞 F) F)ˣ) (v : HeightOneSpectrum (𝓞 F)),
      ((u⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v *
        (u : FiniteAdeleRing (𝓞 F) F) v = 1 := by
    intro u v; rw [← hmul, inv_mul_cancel, hone]
  let U : Subgroup (FiniteAdeleRing (𝓞 F) F)ˣ :=
    { carrier := {u | (∀ v, ‖(u : FiniteAdeleRing (𝓞 F) F) v‖ = 1) ∧
        ∀ v ∈ I, ‖(u : FiniteAdeleRing (𝓞 F) F) v - 1‖ < ε v}
      mul_mem' := by
        rintro u w ⟨hu1, hu2⟩ ⟨hw1, hw2⟩
        refine ⟨fun v => by rw [hmul, norm_mul, hu1, hw1, one_mul], fun v hv => ?_⟩
        rw [hmul]
        have : (u : FiniteAdeleRing (𝓞 F) F) v * (w : FiniteAdeleRing (𝓞 F) F) v - 1 =
            (u : FiniteAdeleRing (𝓞 F) F) v * ((w : FiniteAdeleRing (𝓞 F) F) v - 1) +
              ((u : FiniteAdeleRing (𝓞 F) F) v - 1) := by ring
        rw [this]
        refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ (hu2 v hv))
        rw [norm_mul, hu1 v, one_mul]; exact hw2 v hv
      one_mem' := ⟨fun v => by rw [hone, norm_one],
        fun v _ => by rw [hone, sub_self, norm_zero]; exact hε0 v⟩
      inv_mem' := by
        rintro u ⟨hu1, hu2⟩
        have hn : ∀ v, ‖((u⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v‖ = 1 := by
          intro v
          have := congrArg norm (hinv u v)
          rw [norm_mul, hu1 v, mul_one, norm_one] at this
          exact this
        refine ⟨hn, fun v hv => ?_⟩
        have : ((u⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v - 1 =
            ((u⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v *
              (1 - (u : FiniteAdeleRing (𝓞 F) F) v) := by
          rw [mul_sub, mul_one, hinv]
        rw [this, norm_mul, hn v, one_mul, norm_sub_rev]
        exact hu2 v hv }
  have hUN : ∀ u ∈ U, (u : FiniteAdeleRing (𝓞 F) F) ∈ N := by
    rintro u ⟨hu1, hu2⟩
    apply hεN (u : FiniteAdeleRing (𝓞 F) F)
    · intro v
      have h := IsUltrametricDist.norm_add_le_max ((u : FiniteAdeleRing (𝓞 F) F) v) (-1)
      rw [← sub_eq_add_neg, norm_neg, hu1 v, norm_one, max_self] at h
      exact h
    · exact hu2
  refine ⟨U, ?_, fun u hu => hu.1, fun u hu => hNV u (hUN u hu) (hUN _ (U.inv_mem hu))⟩
  have hopen : ∀ v : HeightOneSpectrum (𝓞 F),
      IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    fun v => Valued.isOpen_valuationSubring _
  have hA : IsOpen {x : FiniteAdeleRing (𝓞 F) F | ∀ v, x v ∈ v.adicCompletionIntegers F} :=
    RestrictedProduct.isOpen_forall_mem hopen
  have hev : ∀ v : HeightOneSpectrum (𝓞 F),
      Continuous fun u : (FiniteAdeleRing (𝓞 F) F)ˣ => (u : FiniteAdeleRing (𝓞 F) F) v :=
    fun v => (RestrictedProduct.continuous_eval v).comp Units.continuous_val
  set O' : Set (FiniteAdeleRing (𝓞 F) F)ˣ :=
    ((Units.val ⁻¹' {x : FiniteAdeleRing (𝓞 F) F | ∀ v, x v ∈ v.adicCompletionIntegers F}) ∩
      ((fun u : (FiniteAdeleRing (𝓞 F) F)ˣ => ((u⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) :
        FiniteAdeleRing (𝓞 F) F)) ⁻¹'
        {x : FiniteAdeleRing (𝓞 F) F | ∀ v, x v ∈ v.adicCompletionIntegers F})) ∩
      ⋂ v ∈ I, {u : (FiniteAdeleRing (𝓞 F) F)ˣ | ‖(u : FiniteAdeleRing (𝓞 F) F) v - 1‖ < ε v}
    with hO'
  have hO'o : IsOpen O' :=
    ((hA.preimage Units.continuous_val).inter (hA.preimage Units.continuous_coe_inv)).inter
      (hI.isOpen_biInter fun v _ =>
        isOpen_lt (continuous_norm.comp ((hev v).sub continuous_const)) continuous_const)
  have h1O' : (1 : (FiniteAdeleRing (𝓞 F) F)ˣ) ∈ O' := by
    refine ⟨⟨fun v => ?_, fun v => ?_⟩, Set.mem_iInter₂.2 fun v _ => ?_⟩
    · exact one_mem _
    · show (((1 : (FiniteAdeleRing (𝓞 F) F)ˣ)⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) :
          FiniteAdeleRing (𝓞 F) F) v ∈ _
      rw [inv_one]; exact one_mem _
    · show ‖((1 : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v - 1‖ < ε v
      rw [hone, sub_self, norm_zero]; exact hε0 v
  have hO'U : O' ⊆ (U : Set (FiniteAdeleRing (𝓞 F) F)ˣ) := by
    rintro u ⟨⟨h1, h2⟩, h3⟩
    refine ⟨fun v => ?_, fun v hv => Set.mem_iInter₂.1 h3 v hv⟩
    have a1 : ‖(u : FiniteAdeleRing (𝓞 F) F) v‖ ≤ 1 := (Valued.toNormedField.norm_le_one_iff).2 (h1 v)
    have a2 : ‖((u⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v‖ ≤ 1 :=
      (Valued.toNormedField.norm_le_one_iff).2 (h2 v)
    have a3 := congrArg norm (hinv u v)
    rw [norm_mul, norm_one] at a3
    nlinarith [norm_nonneg ((u : FiniteAdeleRing (𝓞 F) F) v),
      norm_nonneg (((u⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v)]
  exact Subgroup.isOpen_of_mem_nhds U (g := 1)
    (Filter.mem_of_superset (hO'o.mem_nhds h1O') hO'U)

open Classical in
/-- The real numbers inside the completion at an infinite place. -/
noncomputable def realEmb (w : InfinitePlace F) : ℝ →+* w.Completion :=
  if hw : w.IsReal then (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom
  else ((InfinitePlace.Completion.ringEquivComplexOfIsComplex
    (InfinitePlace.not_isReal_iff_isComplex.1 hw)).symm.toRingHom).comp Complex.ofRealHom

omit [NumberField F] in
lemma norm_realEmb (w : InfinitePlace F) (t : ℝ) : ‖realEmb w t‖ = |t| := by
  unfold realEmb
  split_ifs with hw
  · change ‖(InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm t‖ = |t|
    rw [(InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.isometry.norm_map_of_map_zero
      (map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm), Real.norm_eq_abs]
  · have hc := InfinitePlace.not_isReal_iff_isComplex.1 hw
    change ‖(InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc).symm (t : ℂ)‖ = |t|
    rw [(InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc).symm.isometry.norm_map_of_map_zero
      (map_zero (InfinitePlace.Completion.ringEquivComplexOfIsComplex hc).symm), Complex.norm_real,
      Real.norm_eq_abs]

omit [NumberField F] in
lemma continuous_realEmb (w : InfinitePlace F) : Continuous (realEmb w) := by
  unfold realEmb
  split_ifs with hw
  · exact (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.continuous
  · exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
      (InfinitePlace.not_isReal_iff_isComplex.1 hw)).symm.continuous.comp Complex.continuous_ofReal

/-- (R2) the identity component of the norm-one ideles contains the norm-one archimedean
ideles near `1`. -/
lemma exists_arch_nhds (J : Subgroup (IdeleGroup F)) (hJ : ∀ g : IdeleGroup F, g ∈ J ↔ ideleNorm g = 1) :
    ∃ B : Set (InfiniteAdeleRing F)ˣ, IsOpen B ∧ (1 : (InfiniteAdeleRing F)ˣ) ∈ B ∧
      ∀ a ∈ B, (∏ w : InfinitePlace F, ‖(a : InfiniteAdeleRing F) w‖ ^ w.mult) = 1 →
        iInf a ∈ (Subgroup.connectedComponentOfOne J).map J.subtype := by
  classical
  set d : ℕ := ∑ w : InfinitePlace F, w.mult with hd
  have hd0 : 0 < d := by
    rw [hd, InfinitePlace.sum_mult_eq]; exact Module.finrank_pos
  refine ⟨{a | ∀ w, ‖(a : InfiniteAdeleRing F) w - 1‖ < 1 / 2}, ?_, ?_, ?_⟩
  · have : {a : (InfiniteAdeleRing F)ˣ | ∀ w, ‖(a : InfiniteAdeleRing F) w - 1‖ < 1 / 2} =
        ⋂ w, {a : (InfiniteAdeleRing F)ˣ | ‖(a : InfiniteAdeleRing F) w - 1‖ < 1 / 2} := by
      ext; simp
    rw [this]
    have h1 : ∀ w : InfinitePlace F, Continuous (fun x : InfiniteAdeleRing F => x w) :=
      fun w => continuous_apply w
    have h2 : ∀ w : InfinitePlace F,
        Continuous (fun a : (InfiniteAdeleRing F)ˣ => (a : InfiniteAdeleRing F) w) :=
      fun w => (h1 w).comp (Units.continuous_val (M := InfiniteAdeleRing F))
    exact isOpen_iInter_of_finite fun w => isOpen_lt (continuous_norm.comp
      ((h2 w).sub continuous_const)) continuous_const
  · intro w
    show ‖(1 : w.Completion) - 1‖ < 1 / 2
    rw [sub_self, norm_zero]; norm_num
  intro a ha hna
  let b : unitInterval → InfiniteAdeleRing F := fun s w =>
    1 + realEmb w s * ((a : InfiniteAdeleRing F) w - 1)
  have hb : ∀ s w, 1 / 2 ≤ ‖b s w‖ := by
    intro s w
    have h1 : (1 : w.Completion) = b s w - realEmb w s * ((a : InfiniteAdeleRing F) w - 1) := by
      simp [b]
    have h2 := norm_sub_le (b s w) (realEmb w s * ((a : InfiniteAdeleRing F) w - 1))
    rw [← h1, norm_one, norm_mul, norm_realEmb, abs_of_nonneg s.2.1] at h2
    have h3 : (s : ℝ) * ‖(a : InfiniteAdeleRing F) w - 1‖ ≤ 1 / 2 := by
      have := ha w
      nlinarith [s.2.1, s.2.2, norm_nonneg ((a : InfiniteAdeleRing F) w - 1)]
    linarith
  have hb0 : ∀ s w, b s w ≠ 0 := fun s w h => by
    have := hb s w; rw [h, norm_zero] at this; norm_num at this
  let nb : unitInterval → ℝ := fun s => ∏ w : InfinitePlace F, ‖b s w‖ ^ w.mult
  have hnb : ∀ s, 0 < nb s := fun s =>
    Finset.prod_pos fun w _ => pow_pos (lt_of_lt_of_le (by norm_num) (hb s w)) _
  let c : unitInterval → ℝ := fun s => nb s ^ (-(1 / (d : ℝ)))
  have hc : ∀ s, 0 < c s := fun s => Real.rpow_pos_of_pos (hnb s) _
  let p : unitInterval → InfiniteAdeleRing F := fun s w => realEmb w (c s) * b s w
  have hp0 : ∀ s w, p s w ≠ 0 := fun s w => mul_ne_zero (by
      intro h
      have := norm_realEmb w (c s)
      rw [h, norm_zero, abs_of_pos (hc s)] at this
      linarith [hc s]) (hb0 s w)
  let q : unitInterval → (InfiniteAdeleRing F)ˣ := fun s =>
    ⟨p s, fun w => (p s w)⁻¹, funext fun w => mul_inv_cancel₀ (hp0 s w),
      funext fun w => inv_mul_cancel₀ (hp0 s w)⟩
  have hbc : ∀ w, Continuous fun s : unitInterval => b s w := fun w =>
    continuous_const.add (((continuous_realEmb w).comp continuous_subtype_val).mul continuous_const)
  have hnbc : Continuous nb :=
    continuous_finsetProd _ fun w _ => (continuous_norm.comp (hbc w)).pow _
  have hcc : Continuous c := hnbc.rpow_const fun s => Or.inl (hnb s).ne'
  have hpc : ∀ w, Continuous fun s => p s w := fun w =>
    ((continuous_realEmb w).comp hcc).mul (hbc w)
  have hq : Continuous q := Units.continuous_iff.2
    ⟨continuous_pi hpc, continuous_pi fun w => (hpc w).inv₀ (fun s => hp0 s w)⟩
  have hnorm : ∀ s, ∏ w : InfinitePlace F, ‖(q s : InfiniteAdeleRing F) w‖ ^ w.mult = 1 := by
    intro s
    show ∏ w : InfinitePlace F, ‖realEmb w (c s) * b s w‖ ^ w.mult = 1
    simp_rw [norm_mul, norm_realEmb, abs_of_pos (hc s), mul_pow]
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, ← hd]
    show (nb s ^ (-(1 / (d : ℝ)))) ^ d * nb s = 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hnb s).le]
    have hdr : (d : ℝ) ≠ 0 := by exact_mod_cast hd0.ne'
    rw [show (-(1 / (d : ℝ))) * (d : ℝ) = -1 by field_simp, Real.rpow_neg_one,
      inv_mul_cancel₀ (hnb s).ne']
  let γ : unitInterval → J := fun s =>
    ⟨iInf (q s), (hJ _).2 (by rw [ideleNorm_iInf]; exact hnorm s)⟩
  have hγ : Continuous γ := (continuous_iInf.comp hq).subtype_mk _
  have hq0 : q 0 = 1 := by
    apply Units.ext; funext w
    show realEmb w (c 0) * b 0 w = 1
    have hb0' : ∀ w, b 0 w = 1 := fun w => by simp [b]
    have : nb 0 = 1 := by simp only [nb, hb0', norm_one, one_pow, Finset.prod_const_one]
    simp only [c, this, Real.one_rpow, map_one, hb0', mul_one]
  have hq1 : q 1 = a := by
    apply Units.ext; funext w
    show realEmb w (c 1) * b 1 w = (a : InfiniteAdeleRing F) w
    have hb1 : ∀ w, b 1 w = (a : InfiniteAdeleRing F) w := fun w => by simp [b]
    have : nb 1 = 1 := by simp only [nb, hb1]; exact hna
    simp only [c, this, Real.one_rpow, map_one, hb1, one_mul]
  have hγ0 : γ 0 = 1 := Subtype.ext (by show iInf (q 0) = 1; rw [hq0, map_one])
  have hmem : γ 1 ∈ connectedComponent (1 : J) := by
    rw [← hγ0]
    exact (isPreconnected_range hγ).subset_connectedComponent ⟨0, rfl⟩ ⟨1, rfl⟩
  refine ⟨γ 1, hmem, ?_⟩
  show iInf (q 1) = iInf a
  rw [hq1]

/-- The identity component of `C_F^1` is the closure of the image of the identity component of
the norm-one ideles. -/
theorem connectedComponentOfOne_eq_closure (J : Subgroup (IdeleGroup F))
    (hJ : ∀ g : IdeleGroup F, g ∈ J ↔ ideleNorm g = 1) (K : Subgroup (IdeleClassGroup F))
    (hK : ∀ x : IdeleClassGroup F,
      x ∈ K ↔ ∃ g : IdeleGroup F, (QuotientGroup.mk g : IdeleClassGroup F) = x ∧ ideleNorm g = 1) :
    (Subgroup.connectedComponentOfOne K).map K.subtype =
      (((Subgroup.connectedComponentOfOne J).map J.subtype).map
        (QuotientGroup.mk' (principalIdeles F))).topologicalClosure := by
  set L := (((Subgroup.connectedComponentOfOne J).map J.subtype).map
        (QuotientGroup.mk' (principalIdeles F))) with hLdef
  have hKmem : ∀ x : IdeleClassGroup F, x ∈ K ↔ classNorm F x = 1 := by
    intro x
    rw [hK]
    constructor
    · rintro ⟨g, rfl, hg⟩; exact hg
    · intro hx
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
      exact ⟨g, rfl, hx⟩
  have hKclosed : IsClosed (K : Set (IdeleClassGroup F)) := by
    have : (K : Set (IdeleClassGroup F)) = classNorm F ⁻¹' {1} := by
      ext x; exact hKmem x
    rw [this]
    exact isClosed_singleton.preimage continuous_classNorm
  apply le_antisymm
  · apply cc_le_closure K L
    intro W hW
    have hV : (QuotientGroup.mk : IdeleGroup F → IdeleClassGroup F) ⁻¹' W ∈ nhds (1 : IdeleGroup F) := by
      apply (QuotientGroup.continuous_mk (N := principalIdeles F)).continuousAt.preimage_mem_nhds
      simpa using hW
    have hVf : iFin ⁻¹' ((QuotientGroup.mk : IdeleGroup F → IdeleClassGroup F) ⁻¹' W) ∈
        nhds (1 : (FiniteAdeleRing (𝓞 F) F)ˣ) := by
      apply continuous_iFin.continuousAt.preimage_mem_nhds
      simpa using hV
    obtain ⟨U, hUo, hUn, hUV⟩ := exists_openSubgroup _ hVf
    obtain ⟨B, hBo, hB1, hBJ⟩ := exists_arch_nhds J hJ
    refine ⟨(((Subgroup.connectedComponentOfOne J).map J.subtype) ⊔ U.map iFin).map
      (QuotientGroup.mk' (principalIdeles F)), Subgroup.map_mono le_sup_left, ?_, ?_, ?_⟩
    · rw [Subgroup.map_le_iff_le_comap]
      apply sup_le
      · rintro _ ⟨j, -, rfl⟩
        exact (hK _).2 ⟨j, rfl, (hJ _).1 j.2⟩
      · rintro _ ⟨u, hu, rfl⟩
        exact (hK _).2 ⟨iFin u, rfl, ideleNorm_iFin u (hUn u hu)⟩
    · apply Subgroup.isOpen_of_mem_nhds _ (g := (1 : K))
      set Ut : Set (IdeleGroup F) := split ⁻¹' (B ×ˢ (U : Set (FiniteAdeleRing (𝓞 F) F)ˣ)) with hUt
      have hUto : IsOpen Ut := (hBo.prod hUo).preimage split.continuous
      have hUt1 : (1 : IdeleGroup F) ∈ Ut := by
        have : split (1 : IdeleGroup F) = 1 := by rw [split_apply]; exact map_one _
        show split (1 : IdeleGroup F) ∈ B ×ˢ (U : Set (FiniteAdeleRing (𝓞 F) F)ˣ)
        rw [this]
        exact ⟨hB1, U.one_mem⟩
      have hmo : IsOpen ((QuotientGroup.mk : IdeleGroup F → IdeleClassGroup F) '' Ut) :=
        QuotientGroup.isOpenMap_coe _ hUto
      refine Filter.mem_of_superset ((hmo.preimage continuous_subtype_val).mem_nhds ⟨1, hUt1, rfl⟩) ?_
      rintro x ⟨g, hgU, hgx⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, ← hgx]
      have hg1 : ideleNorm g = 1 := by
        have := (hKmem x).1 x.2
        rw [← hgx] at this
        exact this
      have hdec := eq_iInf_mul_iFin g
      have hgU' : (split g).1 ∈ B ∧ (split g).2 ∈ U := hgU
      have hnorm : (∏ w : InfinitePlace F, ‖((split g).1 : InfiniteAdeleRing F) w‖ ^ w.mult) = 1 := by
        calc (∏ w : InfinitePlace F, ‖((split g).1 : InfiniteAdeleRing F) w‖ ^ w.mult)
            = ideleNorm (iInf (split g).1) * ideleNorm (iFin (split g).2) := by
              rw [ideleNorm_iInf, ideleNorm_iFin _ (hUn _ hgU'.2), mul_one]
          _ = ideleNorm g := by rw [← ideleNorm_mul', ← hdec]
          _ = 1 := hg1
      refine Subgroup.mem_map_of_mem _ ?_
      rw [hdec]
      exact Subgroup.mul_mem_sup (hBJ _ hgU'.1 hnorm) (Subgroup.mem_map_of_mem _ hgU'.2)
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hy
      obtain ⟨u, hu, rfl⟩ := hb
      refine ⟨QuotientGroup.mk' _ a, Subgroup.mem_map_of_mem _ ha, QuotientGroup.mk' _ (iFin u),
        hUV hu, map_mul _ _ _⟩
  · -- the image of the identity component of `J` lies in the identity component of `K`
    let φ : J → K := fun j => ⟨QuotientGroup.mk (j : IdeleGroup F), (hK _).2 ⟨j, rfl, (hJ _).1 j.2⟩⟩
    have hφ : Continuous φ :=
      ((QuotientGroup.continuous_mk (N := principalIdeles F)).comp continuous_subtype_val).subtype_mk _
    have hφ1 : φ 1 = 1 := Subtype.ext rfl
    have hLM : L ≤ (Subgroup.connectedComponentOfOne K).map K.subtype := by
      rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
      have h1 : φ j ∈ connectedComponent (φ 1) :=
        hφ.image_connectedComponent_subset 1 ⟨j, hj, rfl⟩
      rw [hφ1] at h1
      exact ⟨φ j, h1, rfl⟩
    apply Subgroup.topologicalClosure_minimal L hLM
    rw [Subgroup.coe_map]
    exact hKclosed.isClosedEmbedding_subtypeVal.isClosedMap _ isClosed_connectedComponent

/-- A subgroup `H` of a subgroup `K` of a topological group `G`, with the topology induced from `K`,
is isomorphic as a topological group to its image in `G`, with the topology induced from `G`. -/
def subgroupMapSubtypeEquiv {G : Type*} [Group G] [TopologicalSpace G] (K : Subgroup G)
    (H : Subgroup K) : H ≃ₜ* (H.map K.subtype : Subgroup G) where
  toFun x := ⟨((x : K) : G), Subgroup.mem_map_of_mem _ x.2⟩
  invFun y := ⟨⟨(y : G), Subgroup.map_subtype_le H y.2⟩, by
    obtain ⟨k, hk, hky⟩ := Subgroup.mem_map.1 y.2
    have : k = ⟨(y : G), Subgroup.map_subtype_le H y.2⟩ := Subtype.ext hky
    exact this ▸ hk⟩
  left_inv x := rfl
  right_inv y := rfl
  map_mul' x y := rfl
  continuous_toFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    (continuous_subtype_val.subtype_mk _).subtype_mk _

end Sol_MasulloGRH_normOneIdeleClassGroup_connectedComponentOfOne_equiv

open MasulloGRH Sol_MasulloGRH_normOneIdeleClassGroup_connectedComponentOfOne_equiv in
theorem solution (F : Type*) [Field F]
    [NumberField F] (K : Subgroup (IdeleClassGroup F))
    (hK : ∀ x : IdeleClassGroup F,
      x ∈ K ↔ ∃ g : IdeleGroup F, (QuotientGroup.mk g : IdeleClassGroup F) = x ∧ ideleNorm g = 1) :
    Nonempty (Subgroup.connectedComponentOfOne K ≃ₜ*
      Multiplicative ((Fin (InfinitePlace.nrComplexPlaces F) → UnitAddCircle) ×
        (Fin (InfinitePlace.nrRealPlaces F + InfinitePlace.nrComplexPlaces F - 1) →
          AdeleRing (𝓞 ℚ) ℚ ⧸ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)).range.toAddSubgroup))) := by
  -- the group of norm-one ideles
  let J : Subgroup (IdeleGroup F) := (Sol_MasulloGRH_normOneIdeleClassGroup_connectedComponentOfOne_equiv.normHom F).ker
  have hJ : ∀ g : IdeleGroup F, g ∈ J ↔ ideleNorm g = 1 := fun g => by
    rw [MonoidHom.mem_ker, Sol_MasulloGRH_normOneIdeleClassGroup_connectedComponentOfOne_equiv.normHom_apply]
  -- the computation of the closure of the image of the identity component of `J` (child)
  obtain ⟨e⟩ := closure_image_connectedComponentOfOne_normOneIdeles_equiv F J hJ
  -- the identity component of `C_F^1` is that closure (proved above)
  have hD := connectedComponentOfOne_eq_closure J hJ K hK
  let f := subgroupMapSubtypeEquiv K (Subgroup.connectedComponentOfOne K)
  rw [hD] at f
  exact ⟨f.trans e⟩
