-- Prove2me | solution 1 for MasulloGRH.tateIdeleDomain_relCompact_and_interior_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:59:23.701705+00:00
-- url     : https://prove2.me/submissions/60b1635c-0256-4073-9322-9cb06df05bf6

import Mathlib
import Definitions.Def_MasulloGRH_TateIdeleDomain
import Theorems.Thm_MasulloGRH_tateArchimedeanDomain_relCompact_and_interior_nonempty

open NumberField IsDedekindDomain

set_option autoImplicit false
set_option maxSynthPendingDepth 8

namespace Sol_MasulloGRH_tateIdeleDomain_relCompact_and_interior_nonempty

open MasulloGRH RiemannMasullo
open Filter IsLocalRing Topology
open scoped WithZero NNReal

variable {F : Type*} [Field F] [NumberField F]

/-! ### Compactness of the local rings of integers -/

/-- The residue field of a completion at a height-one prime is isomorphic to the quotient
of the ring of integers by that prime. -/
theorem nonempty_residueFieldEquiv_adicCompletion (v : HeightOneSpectrum (𝓞 F)) :
    Nonempty ((𝓞 F ⧸ v.asIdeal) ≃+* ResidueField (v.adicCompletionIntegers F)) := by
  let O := v.adicCompletionIntegers F
  let f := (residue O).comp (algebraMap (𝓞 F) O)
  let q : 𝓞 F ⧸ v.asIdeal →+* ResidueField O := Ideal.Quotient.lift v.asIdeal f (by
    intro r hr
    rw [RingHom.comp_apply, residue_eq_zero_iff]
    apply (Valuation.mem_maximalIdeal_iff _ (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰)).2
    change Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) r) < (1 : ℤᵐ⁰)
    have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := F) v r
    exact h.trans_lt ((v.valuation_lt_one_iff_mem r).2 hr))
  let := Ideal.Quotient.field v.asIdeal
  refine ⟨RingEquiv.ofBijective q ⟨q.injective, ?_⟩⟩
  intro y
  obtain ⟨x, rfl⟩ := residue_surjective y
  -- Approximate the representative first by an element of `F`, then by one of `𝓞 F`.
  let ν : Valuation (v.adicCompletion F) ℤᵐ⁰ := Valued.v
  have hn : {z | ν (z - (x : v.adicCompletion F)) < 1} ∈ 𝓝 (x : v.adicCompletion F) := by
    refine Valued.mem_nhds.mpr ⟨1, ?_⟩
    intro z hz
    simpa using hz
  obtain ⟨a, ha⟩ := (v.denseRange_algebraMap F).mem_nhds hn
  change ν (algebraMap F (v.adicCompletion F) a - x) < 1 at ha
  have ha' : v.valuation F a ≤ 1 := by
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    change ν (algebraMap F (v.adicCompletion F) a) ≤ 1
    simpa only [sub_add_cancel] using ν.map_add_le ha.le x.property
  obtain ⟨r, hr⟩ := v.exists_valuation_sub_lt_of_integer ha' 1
  have hr' : ν (algebraMap (𝓞 F) (v.adicCompletion F) r - algebraMap F (v.adicCompletion F) a) < 1 := by
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F), ← map_sub]
    change Valued.v (((algebraMap (𝓞 F) F) r - a : F) : v.adicCompletion F) < (1 : ℤᵐ⁰)
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    simpa only [Units.val_one] using hr
  refine ⟨Ideal.Quotient.mk _ r, sub_eq_zero.mp ?_⟩
  change residue O (algebraMap (𝓞 F) O r) - residue O x = 0
  rw [← map_sub, residue_eq_zero_iff]
  apply (Valuation.mem_maximalIdeal_iff _ ν).2
  change ν (algebraMap (𝓞 F) (v.adicCompletion F) r - x) < 1
  simpa only [sub_add_sub_cancel] using ν.map_add_lt hr' ha

/-- The residue field of the completion at a height-one prime is finite. -/
theorem finite_residueField_adicCompletion (v : HeightOneSpectrum (𝓞 F)) :
    Finite (ResidueField (v.adicCompletionIntegers F)) := by
  obtain ⟨e⟩ := nonempty_residueFieldEquiv_adicCompletion (F := F) v
  have : Finite (𝓞 F ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  exact Finite.of_equiv _ e.toEquiv

/-- The ring of integers of the completion at a height-one prime is compact. -/
theorem isCompact_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 F)) :
    IsCompact (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  have hclosed : IsClosed (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    Valued.isClosed_valuationSubring _
  have hcomplete : CompleteSpace (v.adicCompletionIntegers F) := hclosed.completeSpace_coe
  exact isCompact_iff_compactSpace.mpr
    (Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.mpr
      ⟨hcomplete, inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers F)),
        finite_residueField_adicCompletion v⟩)


/-! ### The idelic norm -/

/-- The finite component at `v` of an idele times that of its inverse is `1`. -/
lemma fin_mul_inv (g : IdeleGroup F) (v : HeightOneSpectrum (𝓞 F)) :
    (g : AdeleRing (𝓞 F) F).2 v * ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v = 1 := by
  have h : (g : AdeleRing (𝓞 F) F) * ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F) = 1 := g.mul_inv
  have h2 := congrArg (fun a : AdeleRing (𝓞 F) F => a.2 v) h
  exact h2

/-- The component at an infinite place `w` of an idele times that of its inverse is `1`. -/
lemma inf_mul_inv (g : IdeleGroup F) (w : InfinitePlace F) :
    (g : AdeleRing (𝓞 F) F).1 w * ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).1 w = 1 := by
  have h : (g : AdeleRing (𝓞 F) F) * ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F) = 1 := g.mul_inv
  have h2 := congrArg (fun a : AdeleRing (𝓞 F) F => a.1 w) h
  exact h2

/-- If the `v`-components of an idele and of its inverse are both `v`-integral, the `v`-component
has norm `1`. -/
lemma norm_fin_eq_one_of_mem (g : IdeleGroup F) (v : HeightOneSpectrum (𝓞 F))
    (h1 : (g : AdeleRing (𝓞 F) F).2 v ∈ v.adicCompletionIntegers F)
    (h2 : ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v ∈ v.adicCompletionIntegers F) :
    ‖(g : AdeleRing (𝓞 F) F).2 v‖ = 1 := by
  have a1 : ‖(g : AdeleRing (𝓞 F) F).2 v‖ ≤ 1 :=
    Valued.toNormedField.norm_le_one_iff.mpr ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp h1)
  have a2 : ‖((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v‖ ≤ 1 :=
    Valued.toNormedField.norm_le_one_iff.mpr ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp h2)
  have hm : ‖(g : AdeleRing (𝓞 F) F).2 v‖ * ‖((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v‖ = 1 := by
    rw [← norm_mul, fin_mul_inv, norm_one]
  refine le_antisymm a1 ?_
  calc (1 : ℝ) = ‖(g : AdeleRing (𝓞 F) F).2 v‖ * ‖((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v‖ := hm.symm
    _ ≤ ‖(g : AdeleRing (𝓞 F) F).2 v‖ * 1 := mul_le_mul_of_nonneg_left a2 (norm_nonneg _)
    _ = _ := mul_one _

/-- All but finitely many finite components of an idele have norm `1`. -/
lemma finite_mulSupport_fin (g : IdeleGroup F) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) => ‖(g : AdeleRing (𝓞 F) F).2 v‖).Finite := by
  have h1 : ∀ᶠ v in Filter.cofinite,
      (g : AdeleRing (𝓞 F) F).2 v ∈ v.adicCompletionIntegers F := (g : AdeleRing (𝓞 F) F).2.2
  have h2 : ∀ᶠ v in Filter.cofinite,
      ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v ∈ v.adicCompletionIntegers F :=
    ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2.2
  have h3 := h1.and h2
  rw [Filter.eventually_cofinite] at h3
  refine h3.subset ?_
  intro v hv
  simp only [Function.mem_mulSupport] at hv
  simp only [Set.mem_ofPred_eq]
  intro h
  exact hv (norm_fin_eq_one_of_mem g v h.1 h.2)

/-- The idelic norm is multiplicative. -/
lemma ideleNorm_mul (g h : IdeleGroup F) : ideleNorm (g * h) = ideleNorm g * ideleNorm h := by
  unfold ideleNorm
  have e1 : ∀ w : InfinitePlace F, ((g * h : IdeleGroup F) : AdeleRing (𝓞 F) F).1 w =
      (g : AdeleRing (𝓞 F) F).1 w * (h : AdeleRing (𝓞 F) F).1 w := fun w => rfl
  have e2 : ∀ v : HeightOneSpectrum (𝓞 F), ((g * h : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v =
      (g : AdeleRing (𝓞 F) F).2 v * (h : AdeleRing (𝓞 F) F).2 v := fun v => rfl
  simp only [e1, e2, norm_mul, mul_pow, Finset.prod_mul_distrib]
  rw [finprod_mul_distrib (finite_mulSupport_fin g) (finite_mulSupport_fin h)]
  ring

/-- The finite adeles that are integral at every place form an open set. -/
lemma isOpen_integral :
    IsOpen {a : FiniteAdeleRing (𝓞 F) F | ∀ v, a v ∈ v.adicCompletionIntegers F} :=
  RestrictedProduct.isOpen_forall_mem (fun _ => Valued.isOpen_valuationSubring _)

/-- The idelic norm is continuous at `1`: on the open neighbourhood of ideles `g` such that `g` and
`g⁻¹` are integral at all finite places it equals the (continuous) archimedean part. -/
lemma continuousAt_ideleNorm_one : ContinuousAt (ideleNorm (F := F)) 1 := by
  let U : Set (FiniteAdeleRing (𝓞 F) F) := {a | ∀ v, a v ∈ v.adicCompletionIntegers F}
  have hU : IsOpen U := isOpen_integral
  have h1 : (1 : FiniteAdeleRing (𝓞 F) F) ∈ U := fun v => (v.adicCompletionIntegers F).one_mem
  have hval : Continuous (fun g : IdeleGroup F => (g : AdeleRing (𝓞 F) F).2) :=
    continuous_snd.comp Units.continuous_val
  have hinv : Continuous (fun g : IdeleGroup F => ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2) :=
    continuous_snd.comp Units.continuous_coe_inv
  have hfst : Continuous (fun g : IdeleGroup F => (g : AdeleRing (𝓞 F) F).1) :=
    continuous_fst.comp Units.continuous_val
  have hw : ∀ w : InfinitePlace F, Continuous (fun a : InfiniteAdeleRing F => a w) :=
    fun w => continuous_apply w
  have hInf : Continuous (fun g : IdeleGroup F =>
      ∏ w : InfinitePlace F, ‖(g : AdeleRing (𝓞 F) F).1 w‖ ^ w.mult) :=
    continuous_finsetProd _ fun w _ => ((hw w).comp hfst).norm.pow _
  refine hInf.continuousAt.congr ?_
  filter_upwards [hval.continuousAt (hU.mem_nhds h1), hinv.continuousAt (hU.mem_nhds h1)]
    with g hg hginv
  unfold ideleNorm
  rw [finprod_eq_one_of_forall_eq_one (fun v => norm_fin_eq_one_of_mem g v (hg v) (hginv v)),
    mul_one]

/-- The idelic norm is continuous. -/
lemma continuous_ideleNorm : Continuous (ideleNorm (F := F)) := by
  rw [continuous_iff_continuousAt]
  intro g₀
  have h : (ideleNorm (F := F)) = fun g => ideleNorm g₀ * ideleNorm (g₀⁻¹ * g) := by
    funext g
    rw [← ideleNorm_mul, mul_inv_cancel_left]
  rw [h]
  refine continuousAt_const.mul ?_
  have hm : ContinuousAt (fun g : IdeleGroup F => g₀⁻¹ * g) g₀ :=
    (continuous_const.mul continuous_id).continuousAt
  refine ContinuousAt.comp (g := ideleNorm) ?_ hm
  rw [inv_mul_cancel]
  exact continuousAt_ideleNorm_one


/-! ### Local units -/

/-- The component of an idele at a finite place `v` has valuation `1` if and only if it and the
`v`-component of the inverse idele are `v`-integral. -/
lemma valued_eq_one_iff (g : IdeleGroup F) (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v ((g : AdeleRing (𝓞 F) F).2 v) = 1 ↔
      (g : AdeleRing (𝓞 F) F).2 v ∈ v.adicCompletionIntegers F ∧
        ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v ∈ v.adicCompletionIntegers F := by
  have hm : Valued.v ((g : AdeleRing (𝓞 F) F).2 v) *
      Valued.v (((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v) = 1 := by
    rw [← map_mul, fin_mul_inv, map_one]
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.mem_adicCompletionIntegers]
  constructor
  · intro h
    rw [h, one_mul] at hm
    exact ⟨h.le, hm.le⟩
  · rintro ⟨h1, h2⟩
    refine le_antisymm h1 ?_
    calc (1 : ℤᵐ⁰) = Valued.v ((g : AdeleRing (𝓞 F) F).2 v) *
          Valued.v (((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v) := hm.symm
      _ ≤ Valued.v ((g : AdeleRing (𝓞 F) F).2 v) * 1 := mul_le_mul' le_rfl h2
      _ = _ := mul_one _

/-- The ideles that are units at every finite place form an open subset of the idele group. -/
lemma isOpen_unitSet :
    IsOpen {g : IdeleGroup F | ∀ v : HeightOneSpectrum (𝓞 F),
      Valued.v ((g : AdeleRing (𝓞 F) F).2 v) = 1} := by
  have hval : Continuous (fun g : IdeleGroup F => (g : AdeleRing (𝓞 F) F).2) :=
    continuous_snd.comp Units.continuous_val
  have hinv : Continuous (fun g : IdeleGroup F => ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2) :=
    continuous_snd.comp Units.continuous_coe_inv
  have h := (isOpen_integral.preimage hval).inter ((isOpen_integral (F := F)).preimage hinv)
  convert h using 1
  ext g
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage]
  exact ⟨fun hg => ⟨fun v => ((valued_eq_one_iff g v).mp (hg v)).1,
      fun v => ((valued_eq_one_iff g v).mp (hg v)).2⟩,
    fun hg v => (valued_eq_one_iff g v).mpr ⟨hg.1 v, hg.2 v⟩⟩

/-- On the ideles that are units at every finite place, the idelic norm is the archimedean
norm. -/
lemma ideleNorm_eq_of_units (g : IdeleGroup F)
    (hg : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v ((g : AdeleRing (𝓞 F) F).2 v) = 1) :
    ideleNorm g = ∏ w : InfinitePlace F, ‖(g : AdeleRing (𝓞 F) F).1 w‖ ^ w.mult := by
  unfold ideleNorm
  rw [finprod_eq_one_of_forall_eq_one (fun v => norm_fin_eq_one_of_mem g v
    ((valued_eq_one_iff g v).mp (hg v)).1 ((valued_eq_one_iff g v).mp (hg v)).2), mul_one]

/-- The archimedean idele norm, as a real number, is the product of the normalized absolute
values. -/
lemma coe_infiniteIdeleNorm (g : (InfiniteAdeleRing F)ˣ) :
    (((infiniteIdeleNorm F g : ℝ≥0ˣ) : ℝ≥0) : ℝ) =
      ∏ w : InfinitePlace F, ‖(g : InfiniteAdeleRing F) w‖ ^ w.mult := by
  simp only [infiniteIdeleNorm, MonoidHom.finsetProd_apply, MonoidHom.pow_apply,
    MonoidHom.comp_apply, Units.coe_prod, Units.val_pow_eq_pow_val, NNReal.coe_prod,
    NNReal.coe_pow]
  rfl

/-! ### The splitting of the idele group and the compact set of integral finite ideles -/

/-- The idele group is the product of the archimedean ideles and the finite ideles. -/
noncomputable def split : IdeleGroup F ≃ₜ (InfiniteAdeleRing F)ˣ × (FiniteAdeleRing (𝓞 F) F)ˣ :=
  (Homeomorph.prodUnits : (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)ˣ ≃ₜ _)

lemma split_fst_val (g : IdeleGroup F) :
    (((split g).1 : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F) = (g : AdeleRing (𝓞 F) F).1 :=
  rfl

lemma split_symm_fst (x : (InfiniteAdeleRing F)ˣ × (FiniteAdeleRing (𝓞 F) F)ˣ) :
    (((split (F := F)).symm x : IdeleGroup F) : AdeleRing (𝓞 F) F).1 = (x.1 : InfiniteAdeleRing F) :=
  rfl

lemma split_symm_snd (x : (InfiniteAdeleRing F)ˣ × (FiniteAdeleRing (𝓞 F) F)ˣ) :
    (((split (F := F)).symm x : IdeleGroup F) : AdeleRing (𝓞 F) F).2 =
      (x.2 : FiniteAdeleRing (𝓞 F) F) :=
  rfl

/-- The finite adeles that are integral at every place, as a submonoid. -/
def integralSubmonoid (F : Type*) [Field F] [NumberField F] :
    Submonoid (FiniteAdeleRing (𝓞 F) F) where
  carrier := {a | ∀ v, a v ∈ v.adicCompletionIntegers F}
  mul_mem' := fun {a b} ha hb v => by
    change a v * b v ∈ v.adicCompletionIntegers F
    exact mul_mem (ha v) (hb v)
  one_mem' := fun v => (v.adicCompletionIntegers F).one_mem

/-- The integral finite adeles form a compact set (a product of compact local rings). -/
lemma isCompact_integralSubmonoid :
    IsCompact (integralSubmonoid F : Set (FiniteAdeleRing (𝓞 F) F)) := by
  have : ∀ v : HeightOneSpectrum (𝓞 F),
      CompactSpace ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) := fun v =>
    isCompact_iff_compactSpace.mp (isCompact_adicCompletionIntegers v)
  have h := isCompact_range (RestrictedProduct.isEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (𝓕 := Filter.cofinite)).continuous
  rw [RestrictedProduct.range_structureMap] at h
  have h' : IsCompact {a : FiniteAdeleRing (𝓞 F) F | ∀ v, a v ∈ v.adicCompletionIntegers F} := h
  exact h'


/-! ### The three assertions -/

/-- The elements of `E₀ × 𝒪̂_Fˣ` have idelic norm one. -/
theorem ideleNorm_eq_one_of_mem_unitDomain
    (b : Module.Basis (Fin (Units.rank F)) ℤ (Additive ((𝓞 F)ˣ ⧸ Units.torsion F)))
    (v₀ : InfinitePlace F) (σ : ℂ ≃ₐ[ℝ] ℂ) (e : IdeleGroup F)
    (he : e ∈ tateUnitIdeleDomain F b v₀ σ) : ideleNorm e = 1 := by
  obtain ⟨⟨a, -, hea⟩, hfin⟩ := he
  rw [ideleNorm_eq_of_units e hfin, hea, ← coe_infiniteIdeleNorm,
    MonoidHom.mem_ker.mp a.property]
  rfl

/-- `E_F¹` is contained in the norm-one ideles. -/
theorem subset_normOne
    (b : Module.Basis (Fin (Units.rank F)) ℤ (Additive ((𝓞 F)ˣ ⧸ Units.torsion F)))
    (v₀ : InfinitePlace F) (σ : ℂ ≃ₐ[ℝ] ℂ) (r : ClassGroup (𝓞 F) → IdeleGroup F)
    (hrn : ∀ c : ClassGroup (𝓞 F), ideleNorm (r c) = 1) :
    tateIdeleDomain F b v₀ σ r ⊆ {g | ideleNorm g = 1} := by
  rintro g ⟨c, e, he, rfl⟩
  change ideleNorm (r c * e) = 1
  rw [ideleNorm_mul, hrn c, ideleNorm_eq_one_of_mem_unitDomain b v₀ σ e he, mul_one]

/-- `E_F¹` is contained in a compact subset of the idele group. -/
theorem exists_isCompact_superset
    (b : Module.Basis (Fin (Units.rank F)) ℤ (Additive ((𝓞 F)ˣ ⧸ Units.torsion F)))
    (v₀ : InfinitePlace F) (σ : ℂ ≃ₐ[ℝ] ℂ) (r : ClassGroup (𝓞 F) → IdeleGroup F) :
    ∃ K : Set (IdeleGroup F), IsCompact K ∧ tateIdeleDomain F b v₀ σ r ⊆ K := by
  obtain ⟨-, hA, -⟩ := tateArchimedeanDomain_relCompact_and_interior_nonempty F b v₀ σ
  have hT1 : T1Space (FiniteAdeleRing (𝓞 F) F) :=
    inferInstanceAs (T1Space (RestrictedProduct
      (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
      Filter.cofinite))
  have hS : IsCompact ((integralSubmonoid F).units : Set (FiniteAdeleRing (𝓞 F) F)ˣ) :=
    Submonoid.units_isCompact isCompact_integralSubmonoid
  let K₀ : Set (IdeleGroup F) := split ⁻¹'
    ((closure (Subtype.val '' tateArchimedeanDomain F b v₀ σ : Set (InfiniteAdeleRing F)ˣ)) ×ˢ
      ((integralSubmonoid F).units : Set (FiniteAdeleRing (𝓞 F) F)ˣ))
  have hK₀ : IsCompact K₀ := (split (F := F)).isCompact_preimage.mpr (hA.prod hS)
  refine ⟨⋃ c : ClassGroup (𝓞 F), (fun g : IdeleGroup F => r c * g) '' K₀,
    isCompact_iUnion fun c => hK₀.image (continuous_const.mul continuous_id), ?_⟩
  rintro g ⟨c, e, he, rfl⟩
  refine Set.mem_iUnion.mpr ⟨c, e, ?_, rfl⟩
  obtain ⟨⟨a, ha, hea⟩, hfin⟩ := he
  refine ⟨subset_closure ⟨a, ha, ?_⟩, ?_⟩
  · exact Units.ext hea.symm
  · exact (Submonoid.mem_units_iff (integralSubmonoid F) (split e).2).mpr
      ⟨fun v => ((valued_eq_one_iff e v).mp (hfin v)).1,
        fun v => ((valued_eq_one_iff e v).mp (hfin v)).2⟩

/-- The norm-one ideles are closed in the idele group. -/
theorem isClosed_normOne : IsClosed {g : IdeleGroup F | ideleNorm g = 1} :=
  isClosed_eq continuous_ideleNorm continuous_const

/-- `E_F¹` is relatively compact in the norm-one ideles. -/
theorem relCompact
    (b : Module.Basis (Fin (Units.rank F)) ℤ (Additive ((𝓞 F)ˣ ⧸ Units.torsion F)))
    (v₀ : InfinitePlace F) (σ : ℂ ≃ₐ[ℝ] ℂ) (r : ClassGroup (𝓞 F) → IdeleGroup F) :
    IsCompact (closure
      {g : {g : IdeleGroup F // ideleNorm g = 1} | g.val ∈ tateIdeleDomain F b v₀ σ r}) := by
  obtain ⟨K, hK, hsub⟩ := exists_isCompact_superset b v₀ σ r
  have hemb : IsClosedEmbedding
      (Subtype.val : {g : IdeleGroup F // ideleNorm g = 1} → IdeleGroup F) :=
    (isClosed_normOne (F := F)).isClosedEmbedding_subtypeVal
  exact (hemb.isCompact_preimage hK).closure_of_subset fun g hg => hsub hg

/-- `E_F¹` has non-empty interior in the norm-one ideles. -/
theorem interior_nonempty
    (b : Module.Basis (Fin (Units.rank F)) ℤ (Additive ((𝓞 F)ˣ ⧸ Units.torsion F)))
    (v₀ : InfinitePlace F) (σ : ℂ ≃ₐ[ℝ] ℂ) (r : ClassGroup (𝓞 F) → IdeleGroup F)
    (hr₁ : r 1 = 1) :
    (interior {g : {g : IdeleGroup F // ideleNorm g = 1} |
      g.val ∈ tateIdeleDomain F b v₀ σ r}).Nonempty := by
  obtain ⟨-, -, a, ha⟩ := tateArchimedeanDomain_relCompact_and_interior_nonempty F b v₀ σ
  obtain ⟨W, hW, hW_eq⟩ := isOpen_induced_iff.mp
    (isOpen_interior (s := tateArchimedeanDomain F b v₀ σ))
  let p : IdeleGroup F → (InfiniteAdeleRing F)ˣ := fun g => (split g).1
  have hp : Continuous p := continuous_fst.comp (split (F := F)).continuous
  let U : Set {g : IdeleGroup F // ideleNorm g = 1} := Subtype.val ⁻¹'
    ({g : IdeleGroup F | ∀ v : HeightOneSpectrum (𝓞 F),
        Valued.v ((g : AdeleRing (𝓞 F) F).2 v) = 1} ∩ p ⁻¹' W)
  have hU : IsOpen U := (isOpen_unitSet.inter (hW.preimage hp)).preimage continuous_subtype_val
  have hsub : U ⊆ {g | g.val ∈ tateIdeleDomain F b v₀ σ r} := by
    rintro g ⟨hg1, hg2⟩
    have hnorm : infiniteIdeleNorm F (p g.val) = 1 := by
      apply Units.ext
      apply NNReal.coe_injective
      rw [coe_infiniteIdeleNorm, Units.val_one, NNReal.coe_one]
      have h := g.property
      rw [ideleNorm_eq_of_units g.val hg1] at h
      exact h
    have hx : (⟨p g.val, hnorm⟩ : MonoidHom.ker (infiniteIdeleNorm F)) ∈
        interior (tateArchimedeanDomain F b v₀ σ) := by
      rw [← hW_eq]
      exact hg2
    refine ⟨1, g.val, ⟨⟨⟨p g.val, hnorm⟩, interior_subset hx, rfl⟩, hg1⟩, ?_⟩
    rw [hr₁, one_mul]
  let g₀ : IdeleGroup F := (split (F := F)).symm (a.val, 1)
  have hg₀fin : ∀ v : HeightOneSpectrum (𝓞 F),
      Valued.v ((g₀ : AdeleRing (𝓞 F) F).2 v) = 1 := fun v => map_one _
  have hg₀norm : ideleNorm g₀ = 1 := by
    rw [ideleNorm_eq_of_units g₀ hg₀fin]
    have h := coe_infiniteIdeleNorm (F := F) a.val
    rw [MonoidHom.mem_ker.mp a.property] at h
    exact h.symm
  refine ⟨⟨g₀, hg₀norm⟩, interior_maximal hsub hU ⟨hg₀fin, ?_⟩⟩
  have hpg₀ : p g₀ = a.val := by
    change (split ((split (F := F)).symm (a.val, 1))).1 = a.val
    rw [Homeomorph.apply_symm_apply]
  have haW : a ∈ Subtype.val ⁻¹' W := by
    rw [hW_eq]
    exact ha
  change p g₀ ∈ W
  rw [hpg₀]
  exact haW

end Sol_MasulloGRH_tateIdeleDomain_relCompact_and_interior_nonempty

open MasulloGRH

theorem solution
    (F : Type*) [Field F] [NumberField F]
    (b : Module.Basis (Fin (Units.rank F)) ℤ (Additive ((𝓞 F)ˣ ⧸ Units.torsion F)))
    (v₀ : InfinitePlace F) (σ : ℂ ≃ₐ[ℝ] ℂ)
    (r : ClassGroup (𝓞 F) → IdeleGroup F)
    (hr₁ : r 1 = 1) (hrn : ∀ c : ClassGroup (𝓞 F), ideleNorm (r c) = 1)
    (hr : ∀ c : ClassGroup (𝓞 F), ideleIdealClass F (r c) = c) :
    tateIdeleDomain F b v₀ σ r ⊆ {g | ideleNorm g = 1} ∧
    IsCompact (closure
      {g : {g : IdeleGroup F // ideleNorm g = 1} | g.val ∈ tateIdeleDomain F b v₀ σ r}) ∧
    (interior
      {g : {g : IdeleGroup F // ideleNorm g = 1} |
        g.val ∈ tateIdeleDomain F b v₀ σ r}).Nonempty :=
  ⟨Sol_MasulloGRH_tateIdeleDomain_relCompact_and_interior_nonempty.subset_normOne b v₀ σ r hrn,
    Sol_MasulloGRH_tateIdeleDomain_relCompact_and_interior_nonempty.relCompact b v₀ σ r,
    Sol_MasulloGRH_tateIdeleDomain_relCompact_and_interior_nonempty.interior_nonempty b v₀ σ r hr₁⟩
