-- Prove2me | solution 1 for MasulloGRH.sLocalTheta_asymptotic_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T07:07:52.556553+00:00
-- url     : https://prove2.me/submissions/876e49ef-751d-4cf7-b9d1-3531e505583c

import Definitions.Def_MasulloGRH_SLocalTheta

set_option autoImplicit false

open MasulloGRH NumberField IsDedekindDomain

namespace Aux_MasulloGRH_s_unit_lattice_point_count

open Filter Topology IsLocalRing RestrictedProduct
open scoped WithZero

section Local

variable {F : Type*} [Field F] [NumberField F]

theorem nonempty_residueFieldEquiv (v : HeightOneSpectrum (𝓞 F)) :
    Nonempty ((𝓞 F ⧸ v.asIdeal) ≃+* ResidueField (v.adicCompletionIntegers F)) := by
  let O := v.adicCompletionIntegers F
  let f := (residue O).comp (algebraMap (𝓞 F) O)
  let q : 𝓞 F ⧸ v.asIdeal →+* ResidueField O := Ideal.Quotient.lift v.asIdeal f (by
    intro r hr
    rw [RingHom.comp_apply, residue_eq_zero_iff]
    apply (Valuation.mem_maximalIdeal_iff _ (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰)).2
    change Valued.v ((algebraMap (𝓞 F) F r : F) : v.adicCompletion F) < (1 : ℤᵐ⁰)
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact (v.valuation_lt_one_iff_mem r).2 hr)
  let := Ideal.Quotient.field v.asIdeal
  refine ⟨RingEquiv.ofBijective q ⟨q.injective, ?_⟩⟩
  intro y
  obtain ⟨x, rfl⟩ := residue_surjective y
  let ν : Valuation (v.adicCompletion F) ℤᵐ⁰ := Valued.v
  have hn : {z | ν (z - (x : v.adicCompletion F)) < 1} ∈ 𝓝 (x : v.adicCompletion F) := by
    refine Valued.mem_nhds.mpr ⟨1, ?_⟩
    intro z hz
    simpa only [Set.mem_ofPred_eq, Units.val_one, Valuation.restrict_lt_iff_lt_embedding,
      map_one] using hz
  obtain ⟨a, ha⟩ := (v.denseRange_algebraMap F).mem_nhds hn
  change ν (algebraMap F (v.adicCompletion F) a - x) < 1 at ha
  have ha' : v.valuation F a ≤ 1 := by
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    change ν (algebraMap F (v.adicCompletion F) a) ≤ 1
    simpa only [sub_add_cancel] using ν.map_add_le ha.le x.property
  obtain ⟨r, hr⟩ := v.exists_valuation_sub_lt_of_integer ha' 1
  have hr' : ν (algebraMap (𝓞 F) (v.adicCompletion F) r -
      algebraMap F (v.adicCompletion F) a) < 1 := by
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

theorem finite_residueField (v : HeightOneSpectrum (𝓞 F)) :
    Finite (ResidueField (v.adicCompletionIntegers F)) := by
  obtain ⟨e⟩ := nonempty_residueFieldEquiv v
  have : Finite (𝓞 F ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  exact Finite.of_equiv _ e.toEquiv

theorem properSpace_adicCompletion (v : HeightOneSpectrum (𝓞 F)) :
    ProperSpace (v.adicCompletion F) := by
  have : IsDiscreteValuationRing (v.adicCompletionIntegers F) := inferInstance
  exact (Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
    (Γ₀ := ℤᵐ⁰)).2 ⟨inferInstance, ‹_›, finite_residueField v⟩

theorem compactSpace_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 F)) :
    CompactSpace (v.adicCompletionIntegers F) := by
  have : IsClosed (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    Valued.isClosed_valuationSubring _
  have hcomplete : CompleteSpace (v.adicCompletionIntegers F) := IsClosed.completeSpace_coe
  exact Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.mpr
    ⟨hcomplete, inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers F)),
      finite_residueField v⟩

theorem isCompact_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 F)) :
    IsCompact (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  have := compactSpace_adicCompletionIntegers v
  exact isCompact_iff_compactSpace.mpr this

theorem isOpen_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
  Valued.isOpen_valuationSubring _

instance locallyCompactSpace_adicCompletion (v : HeightOneSpectrum (𝓞 F)) :
    LocallyCompactSpace (v.adicCompletion F) := by
  have := properSpace_adicCompletion v
  infer_instance

instance locallyCompactSpace_finiteAdeleRing : LocallyCompactSpace (FiniteAdeleRing (𝓞 F) F) := by
  have : Fact (∀ v : HeightOneSpectrum (𝓞 F),
      IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    ⟨fun v ↦ isOpen_adicCompletionIntegers v⟩
  exact RestrictedProduct.locallyCompactSpace_of_addGroup _
    (Filter.Eventually.of_forall fun v ↦ isCompact_adicCompletionIntegers v)

instance locallyCompactSpace_adeleRing : LocallyCompactSpace (AdeleRing (𝓞 F) F) := by
  change LocallyCompactSpace (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
  infer_instance

instance t2Space_adeleRing : T2Space (AdeleRing (𝓞 F) F) := by
  have : T2Space (FiniteAdeleRing (𝓞 F) F) :=
    T2Space.of_injective_continuous
      (f := fun x : Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F]
        ↦ (x : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F))
      DFunLike.coe_injective RestrictedProduct.continuous_coe
  have : T2Space (InfiniteAdeleRing F) := by
    change T2Space ((v : InfinitePlace F) → v.Completion)
    infer_instance
  change T2Space (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
  infer_instance


end Local

section RP

variable {ι : Type*} {G : ι → Type*} [∀ i, TopologicalSpace (G i)]

theorem continuous_rp_of_uniform {X : Type*} [TopologicalSpace X]
    {A : (i : ι) → Set (G i)} {f : X → Πʳ i, [G i, A i]}
    (hc : ∀ i, Continuous (fun x ↦ f x i)) (hA : ∀ᶠ i in cofinite, ∀ x, f x i ∈ A i) :
    Continuous f := by
  let S := {i | ∀ x, f x i ∈ A i}
  let lift (x : X) : Πʳ i, [G i, A i]_[𝓟 S] := ⟨f x, fun _ hi ↦ hi x⟩
  have hl : Continuous lift :=
    RestrictedProduct.continuous_rng_of_principal.mpr (continuous_pi hc)
  exact (RestrictedProduct.continuous_inclusion (le_principal_iff.mpr hA)).comp hl

theorem isOpen_rp_forall_mem {A : (i : ι) → Set (G i)} (t : Set ι)
    (ht : ∀ i, IsOpen (A i)) :
    IsOpen {x : Πʳ i, [G i, A i] | ∀ i ∈ t, x i ∈ A i} :=
  RestrictedProduct.isOpen_forall_imp_mem ht (p := fun i ↦ i ∈ t)

variable [∀ i, Monoid (G i)] {S : ι → Type*}
    [∀ i, SetLike (S i) (G i)] [∀ i, SubmonoidClass (S i) (G i)]

theorem unitsEquiv_continuous (B : (i : ι) → S i) (hB : ∀ i, IsOpen (B i : Set (G i))) :
    Continuous (RestrictedProduct.unitsEquiv G (B := B) (𝓕 := cofinite)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  let s := {i | x.val i ∈ B i ∧ x.inv i ∈ B i}
  let V := {y : (Πʳ i, [G i, B i])ˣ | ∀ i ∈ s, y.val i ∈ B i ∧ y.inv i ∈ B i}
  have hs := isOpen_rp_forall_mem (G := G) (A := fun i ↦ (B i : Set (G i))) s hB
  have hV : IsOpen V := by
    convert (hs.preimage Units.continuous_val).inter
      (hs.preimage Units.continuous_coe_inv) using 1
    ext y
    exact ⟨fun h ↦ ⟨fun i hi ↦ (h i hi).1, fun i hi ↦ (h i hi).2⟩,
      fun h i hi ↦ ⟨h.1 i hi, h.2 i hi⟩⟩
  apply ContinuousOn.continuousAt (s := V) _ (hV.mem_nhds fun _ hi ↦ hi)
  apply continuousOn_iff_continuous_domRestrict.mpr
  apply continuous_rp_of_uniform
  · intro i
    exact Units.continuous_iff.mpr
      ⟨(RestrictedProduct.continuous_eval i).comp (Units.continuous_val.comp continuous_subtype_val),
        (RestrictedProduct.continuous_eval i).comp
          (Units.continuous_coe_inv.comp continuous_subtype_val)⟩
  · exact (x.val.2.and x.inv.2).mono fun i hi y ↦ y.2 i hi

theorem unitsEquiv_symm_continuous (B : (i : ι) → S i) :
    Continuous (RestrictedProduct.unitsEquiv G (B := B) (𝓕 := cofinite)).symm := by
  apply Units.continuous_iff.mpr
  exact ⟨RestrictedProduct.mapAlong_continuous (fun i ↦ (G i)ˣ) G id tendsto_id
      (A₁ := fun i ↦ (Submonoid.ofClass (B i)).units) (A₂ := fun i ↦ B i) (fun _ ↦ Units.val)
      (.of_forall fun _ _ hx ↦ hx.1) (fun _ ↦ Units.continuous_val),
    RestrictedProduct.mapAlong_continuous (fun i ↦ (G i)ˣ) G id tendsto_id
      (A₁ := fun i ↦ (Submonoid.ofClass (B i)).units) (A₂ := fun i ↦ B i) (fun _ ↦ Units.inv)
      (.of_forall fun _ _ hx ↦ hx.2) (fun _ ↦ Units.continuous_coe_inv)⟩

end RP

section Norm

variable {F : Type*} [Field F] [NumberField F]

theorem fin_mul_inv (g : IdeleGroup F) (v : HeightOneSpectrum (𝓞 F)) :
    (g : AdeleRing (𝓞 F) F).2 v * ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v = 1 := by
  have h := g.mul_inv
  have := congrArg (fun a : AdeleRing (𝓞 F) F ↦ a.2 v) h
  exact this

theorem norm_eq_one_of_mem {v : HeightOneSpectrum (𝓞 F)} {x y : v.adicCompletion F}
    (hxy : x * y = 1) (hx : x ∈ v.adicCompletionIntegers F) (hy : y ∈ v.adicCompletionIntegers F) :
    ‖x‖ = 1 := by
  have h1 : ‖x‖ ≤ 1 := Valued.toNormedField.norm_le_one_iff.mpr hx
  have h2 : ‖y‖ ≤ 1 := Valued.toNormedField.norm_le_one_iff.mpr hy
  have h3 : ‖x‖ * ‖y‖ = 1 := by rw [← norm_mul, hxy, norm_one]
  have h4 : 0 ≤ ‖x‖ := norm_nonneg _
  have h5 : 0 ≤ ‖y‖ := norm_nonneg _
  nlinarith

theorem fin_norm_pos (g : IdeleGroup F) (v : HeightOneSpectrum (𝓞 F)) :
    0 < ‖(g : AdeleRing (𝓞 F) F).2 v‖ := by
  apply norm_pos_iff.mpr
  intro h
  have := fin_mul_inv g v
  rw [h, zero_mul] at this
  exact zero_ne_one this

theorem eventually_norm_eq_one (g : IdeleGroup F) :
    ∀ᶠ v in cofinite, ‖(g : AdeleRing (𝓞 F) F).2 v‖ = 1 := by
  filter_upwards [(g : AdeleRing (𝓞 F) F).2.2, ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2.2]
    with v h1 h2
  exact norm_eq_one_of_mem (fin_mul_inv g v) h1 h2

theorem hasFiniteMulSupport_norm (g : IdeleGroup F) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) ↦ ‖(g : AdeleRing (𝓞 F) F).2 v‖).Finite := by
  have := eventually_norm_eq_one g
  rw [Filter.eventually_cofinite] at this
  exact this

theorem ideleNorm_mul (g h : IdeleGroup F) : ideleNorm (g * h) = ideleNorm g * ideleNorm h := by
  unfold ideleNorm
  have e1 : ∀ w : InfinitePlace F, ‖((g * h : IdeleGroup F) : AdeleRing (𝓞 F) F).1 w‖ ^ w.mult =
      ‖(g : AdeleRing (𝓞 F) F).1 w‖ ^ w.mult * ‖(h : AdeleRing (𝓞 F) F).1 w‖ ^ w.mult := by
    intro w
    rw [← mul_pow, ← norm_mul]
    rfl
  have e2 : ∀ v : HeightOneSpectrum (𝓞 F), ‖((g * h : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v‖ =
      ‖(g : AdeleRing (𝓞 F) F).2 v‖ * ‖(h : AdeleRing (𝓞 F) F).2 v‖ := by
    intro v
    rw [← norm_mul]
    rfl
  simp only [e1, e2, Finset.prod_mul_distrib]
  rw [finprod_mul_distrib (hasFiniteMulSupport_norm g) (hasFiniteMulSupport_norm h)]
  ring

theorem ideleNorm_pos (g : IdeleGroup F) : 0 < ideleNorm g := by
  unfold ideleNorm
  apply mul_pos
  · apply Finset.prod_pos
    intro w _
    apply pow_pos
    apply norm_pos_iff.mpr
    intro h0
    have h := g.mul_inv
    have := congrArg (fun a : AdeleRing (𝓞 F) F ↦ a.1 w) h
    change (g : AdeleRing (𝓞 F) F).1 w * ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).1 w = 1
      at this
    rw [h0, zero_mul] at this
    exact zero_ne_one this
  · exact finprod_induction (0 < ·) zero_lt_one (fun _ _ ↦ mul_pos) fun v ↦ fin_norm_pos g v

theorem infNorm_continuous : Continuous (fun g : IdeleGroup F ↦
    ∏ w : InfinitePlace F, ‖(g : AdeleRing (𝓞 F) F).1 w‖ ^ w.mult) := by
  have c : Continuous (fun g : IdeleGroup F ↦ ((g : AdeleRing (𝓞 F) F).1 : InfiniteAdeleRing F)) :=
    continuous_fst.comp Units.continuous_val
  apply continuous_finsetProd
  intro w _
  exact (((continuous_apply w).comp c).norm).pow _

theorem isOpen_integralUnits : IsOpen {g : IdeleGroup F | ∀ v : HeightOneSpectrum (𝓞 F),
    (g : AdeleRing (𝓞 F) F).2 v ∈ v.adicCompletionIntegers F ∧
    ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v ∈ v.adicCompletionIntegers F} := by
  have hs := isOpen_rp_forall_mem (G := fun v : HeightOneSpectrum (𝓞 F) ↦ v.adicCompletion F)
    (A := fun v ↦ (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Set.univ
    (fun v ↦ isOpen_adicCompletionIntegers v)
  have c1 : Continuous (fun g : IdeleGroup F ↦ ((g : AdeleRing (𝓞 F) F).2 :
      Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F])) :=
    continuous_snd.comp Units.continuous_val
  have c2 : Continuous (fun g : IdeleGroup F ↦ (((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 :
      Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F])) :=
    continuous_snd.comp Units.continuous_coe_inv
  convert (hs.preimage c1).inter (hs.preimage c2) using 1
  ext g
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_univ, true_implies]
  exact ⟨fun h ↦ ⟨fun v ↦ (h v).1, fun v ↦ (h v).2⟩, fun h v ↦ ⟨h.1 v, h.2 v⟩⟩

theorem ideleNorm_eq_infNorm (g : IdeleGroup F) (hg : ∀ v : HeightOneSpectrum (𝓞 F),
    (g : AdeleRing (𝓞 F) F).2 v ∈ v.adicCompletionIntegers F ∧
    ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v ∈ v.adicCompletionIntegers F) :
    ideleNorm g = ∏ w : InfinitePlace F, ‖(g : AdeleRing (𝓞 F) F).1 w‖ ^ w.mult := by
  unfold ideleNorm
  have : (∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(g : AdeleRing (𝓞 F) F).2 v‖) = 1 :=
    finprod_eq_one_of_forall_eq_one fun v ↦ norm_eq_one_of_mem (fin_mul_inv g v) (hg v).1 (hg v).2
  rw [this, mul_one]

theorem ideleNorm_continuousAt_one : ContinuousAt (ideleNorm : IdeleGroup F → ℝ) 1 := by
  apply (infNorm_continuous (F := F)).continuousAt.congr
  have h1 : (1 : IdeleGroup F) ∈ {g : IdeleGroup F | ∀ v : HeightOneSpectrum (𝓞 F),
      (g : AdeleRing (𝓞 F) F).2 v ∈ v.adicCompletionIntegers F ∧
      ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v ∈ v.adicCompletionIntegers F} := by
    intro v
    rw [inv_one]
    exact ⟨(v.adicCompletionIntegers F).one_mem, (v.adicCompletionIntegers F).one_mem⟩
  filter_upwards [isOpen_integralUnits.mem_nhds h1] with g hg
  exact (ideleNorm_eq_infNorm g hg).symm

theorem ideleNorm_continuous : Continuous (ideleNorm : IdeleGroup F → ℝ) := by
  apply continuous_iff_continuousAt.mpr
  intro g0
  have hm : Continuous (fun g : IdeleGroup F ↦ g0⁻¹ * g) := continuous_const.mul continuous_id
  have hc : ContinuousAt (fun g : IdeleGroup F ↦ ideleNorm (g0⁻¹ * g)) g0 := by
    apply ContinuousAt.comp_of_eq (g := ideleNorm) ideleNorm_continuousAt_one hm.continuousAt
    exact inv_mul_cancel g0
  have h2 : ContinuousAt (fun g : IdeleGroup F ↦ ideleNorm g0 * ideleNorm (g0⁻¹ * g)) g0 :=
    continuousAt_const.mul hc
  convert h2 using 1
  funext g
  rw [← ideleNorm_mul, mul_inv_cancel_left]

end Norm

section Principal

variable {F : Type*} [Field F] [NumberField F]

theorem fin_prod_eq (x : F) (hx : x ≠ 0) :
    ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(x : v.adicCompletion F)‖ = |Algebra.norm ℚ x|⁻¹ := by
  have e : ∀ v : HeightOneSpectrum (𝓞 F), ‖(x : v.adicCompletion F)‖ =
      (FinitePlace.equivHeightOneSpectrum.symm v) x := fun v ↦ rfl
  simp only [e]
  rw [finprod_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := F)).symm
    (f := fun w : FinitePlace F ↦ w x)]
  exact FinitePlace.prod_eq_inv_abs_norm hx

theorem inf_prod_eq (x : F) :
    ∏ w : InfinitePlace F, ‖(x : w.Completion)‖ ^ w.mult = |Algebra.norm ℚ x| := by
  have := InfiniteAdeleRing.coe_norm_eq_abs_norm x
  rw [InfiniteAdeleRing.norm_def] at this
  exact this

theorem product_formula (x : F) (hx : x ≠ 0) :
    (∏ w : InfinitePlace F, ‖(x : w.Completion)‖ ^ w.mult) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(x : v.adicCompletion F)‖ = 1 := by
  rw [inf_prod_eq, fin_prod_eq x hx]
  have hN : Algebra.norm ℚ x ≠ 0 := Algebra.norm_ne_zero_iff.mpr hx
  rw [← Rat.cast_mul, mul_inv_cancel₀ (abs_ne_zero.mpr hN), Rat.cast_one]

theorem ideleNorm_principal (ξ : Fˣ) : ideleNorm (principalIdele F ξ) = 1 :=
  product_formula (ξ : F) ξ.ne_zero


def DU (F : Type*) [Field F] [NumberField F] : Set (IdeleGroup F) :=
  {g | (∏ w : InfinitePlace F, ‖(g : AdeleRing (𝓞 F) F).1 w - 1‖ ^ w.mult) < 1 ∧
    ∀ v : HeightOneSpectrum (𝓞 F), (g : AdeleRing (𝓞 F) F).2 v ∈ v.adicCompletionIntegers F}

theorem isOpen_DU : IsOpen (DU F) := by
  have c : Continuous (fun g : IdeleGroup F ↦ ((g : AdeleRing (𝓞 F) F).1 : InfiniteAdeleRing F)) :=
    continuous_fst.comp Units.continuous_val
  have c0 : Continuous (fun g : IdeleGroup F ↦
      ∏ w : InfinitePlace F, ‖(g : AdeleRing (𝓞 F) F).1 w - 1‖ ^ w.mult) := by
    apply continuous_finsetProd
    intro w _
    exact ((((continuous_apply w).comp c).sub continuous_const).norm).pow _
  have hs := isOpen_rp_forall_mem (G := fun v : HeightOneSpectrum (𝓞 F) ↦ v.adicCompletion F)
    (A := fun v ↦ (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Set.univ
    (fun v ↦ isOpen_adicCompletionIntegers v)
  have c1 : Continuous (fun g : IdeleGroup F ↦ ((g : AdeleRing (𝓞 F) F).2 :
      Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F])) :=
    continuous_snd.comp Units.continuous_val
  convert (isOpen_lt c0 continuous_const).inter (hs.preimage c1) using 1
  ext g
  simp only [DU, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_univ, true_implies]
  rfl

theorem one_mem_DU : (1 : IdeleGroup F) ∈ DU F := by
  refine ⟨?_, fun v ↦ (v.adicCompletionIntegers F).one_mem⟩
  obtain ⟨w0⟩ : Nonempty (InfinitePlace F) := inferInstance
  have h0 : (∏ w : InfinitePlace F, ‖((1 : IdeleGroup F) : AdeleRing (𝓞 F) F).1 w - 1‖ ^ w.mult)
      = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ w0)
    have : ((1 : IdeleGroup F) : AdeleRing (𝓞 F) F).1 w0 - 1 = 0 := sub_self _
    rw [this, norm_zero]
    exact zero_pow (InfinitePlace.mult_pos (w := w0)).ne'
  rw [h0]
  exact zero_lt_one

theorem eq_one_of_principal_mem_DU (ξ : Fˣ) (h : principalIdele F ξ ∈ DU F) : ξ = 1 := by
  by_contra hne
  have hy : (ξ : F) - 1 ≠ 0 := by
    intro h0
    apply hne
    exact Units.ext (sub_eq_zero.mp h0)
  have pf := product_formula ((ξ : F) - 1) hy
  have hinf : (∏ w : InfinitePlace F, ‖(((ξ : F) - 1 : F) : w.Completion)‖ ^ w.mult) < 1 := by
    have e : ∀ w : InfinitePlace F, (((ξ : F) - 1 : F) : w.Completion) =
        ((principalIdele F ξ : IdeleGroup F) : AdeleRing (𝓞 F) F).1 w - 1 := by
      intro w
      show algebraMap F w.Completion ((ξ : F) - 1) = algebraMap F w.Completion (ξ : F) - 1
      rw [map_sub, map_one]
    simp only [e]
    exact h.1
  have hfin : ∀ v : HeightOneSpectrum (𝓞 F), ‖(((ξ : F) - 1 : F) : v.adicCompletion F)‖ ≤ 1 := by
    intro v
    have e : (((ξ : F) - 1 : F) : v.adicCompletion F) =
        ((principalIdele F ξ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v - 1 := by
      show FinitePlace.embedding v ((ξ : F) - 1) = FinitePlace.embedding v (ξ : F) - 1
      rw [map_sub, map_one]
    rw [e]
    apply Valued.toNormedField.norm_le_one_iff.mpr
    exact (v.adicCompletionIntegers F).sub_mem (h.2 v) (v.adicCompletionIntegers F).one_mem
  have hB : (∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(((ξ : F) - 1 : F) : v.adicCompletion F)‖) ≤ 1 := by
    have := finprod_induction (fun a : ℝ ↦ 0 ≤ a ∧ a ≤ 1) ⟨zero_le_one, le_rfl⟩
      (fun a b ha hb ↦ ⟨mul_nonneg ha.1 hb.1, mul_le_one₀ ha.2 hb.1 hb.2⟩)
      (fun v ↦ ⟨norm_nonneg _, hfin v⟩)
    exact this.2
  have hA : 0 ≤ (∏ w : InfinitePlace F, ‖(((ξ : F) - 1 : F) : w.Completion)‖ ^ w.mult) :=
    Finset.prod_nonneg fun w _ ↦ pow_nonneg (norm_nonneg _) _
  have := mul_le_of_le_one_right hA hB
  linarith

theorem isOpen_singleton_one_principal :
    IsOpen ({1} : Set (principalIdeles F)) := by
  convert isOpen_DU.preimage (continuous_subtype_val (p := fun g ↦ g ∈ principalIdeles F)) using 1
  ext x
  simp only [Set.mem_singleton_iff, Set.mem_preimage]
  constructor
  · intro hx
    rw [hx]
    exact one_mem_DU
  · intro hx
    obtain ⟨ξ, hξ⟩ := x.2
    have hξ' : principalIdele F ξ ∈ DU F := by rw [hξ]; exact hx
    have h1 := eq_one_of_principal_mem_DU ξ hξ'
    apply Subtype.ext
    rw [← hξ, h1, map_one]
    rfl

instance discrete_principal : DiscreteTopology (principalIdeles F) :=
  discreteTopology_of_isOpen_singleton_one isOpen_singleton_one_principal

theorem isClosed_principal : IsClosed ((principalIdeles F : Subgroup (IdeleGroup F)) :
    Set (IdeleGroup F)) := Subgroup.isClosed_of_discrete

theorem isClosed_image_principal (A : Set Fˣ) : IsClosed (principalIdele F '' A) := by
  let S : Set (principalIdeles F) := {x | (x : IdeleGroup F) ∈ principalIdele F '' A}
  have hS : IsClosed S := isClosed_discrete S
  have himg : principalIdele F '' A = Subtype.val '' S := by
    ext g
    constructor
    · rintro ⟨ξ, hξ, rfl⟩
      exact ⟨⟨principalIdele F ξ, ⟨ξ, rfl⟩⟩, ⟨ξ, hξ, rfl⟩, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact hx
  rw [himg]
  exact (IsClosed.isClosedEmbedding_subtypeVal isClosed_principal).isClosedMap S hS
end Principal


section Sigma

variable {F : Type*} [Field F] [NumberField F]

omit [NumberField F] in
theorem exists_scalar (v : InfinitePlace F) :
    ∃ f : ℝ →+* v.Completion, Continuous f ∧ ∀ x, ‖f x‖ = ‖x‖ := by
  open InfinitePlace.Completion in
  by_cases hv : v.IsReal
  · let e := ringEquivRealOfIsReal hv
    have hi : Isometry e.symm := (isometryEquivRealOfIsReal hv).symm.isometry
    exact ⟨e.symm, hi.continuous, hi.norm_map_of_map_zero (map_zero e.symm)⟩
  · have hv' := InfinitePlace.not_isReal_iff_isComplex.mp hv
    let e := ringEquivComplexOfIsComplex hv'
    have hi : Isometry e.symm := (isometryEquivComplexOfIsComplex hv').symm.isometry
    exact ⟨e.symm.toRingHom.comp Complex.ofRealHom, hi.continuous.comp Complex.continuous_ofReal,
      fun x ↦ (hi.norm_map_of_map_zero (map_zero e.symm) (x : ℂ)).trans (Complex.norm_real x)⟩

open Classical in
/-- The infinite component used by the section. -/
noncomputable def infComp (v : InfinitePlace F) (f : ℝ →+* v.Completion) (y : ℝ) : InfiniteAdeleRing F :=
  fun w ↦ if h : w = v then h ▸ f (Real.exp (y / v.mult)) else 1

theorem infComp_add (v : InfinitePlace F) (f : ℝ →+* v.Completion) (a b : ℝ) :
    infComp v f (a + b) = infComp v f a * infComp v f b := by
  funext w
  change _ = infComp v f a w * infComp v f b w
  unfold infComp
  by_cases h : w = v
  · subst h
    simp only [↓reduceDIte]
    rw [add_div, Real.exp_add, map_mul]
  · simp only [dif_neg h, mul_one]

theorem infComp_zero (v : InfinitePlace F) (f : ℝ →+* v.Completion) :
    infComp v f 0 = 1 := by
  funext w
  unfold infComp
  by_cases h : w = v
  · subst h
    simp only [↓reduceDIte, zero_div, Real.exp_zero, map_one]
    rfl
  · simp only [dif_neg h]
    rfl

theorem infComp_continuous (v : InfinitePlace F) (f : ℝ →+* v.Completion) (hf : Continuous f) :
    Continuous (infComp v f) := by
  apply continuous_pi
  intro w
  unfold infComp
  by_cases h : w = v
  · subst h
    simp only [↓reduceDIte]
    exact hf.comp (Real.continuous_exp.comp (continuous_id.div_const _))
  · simp only [dif_neg h]
    exact continuous_const

/-- The idele with infinite component `infComp` and finite component `1`. -/
noncomputable def sv (v : InfinitePlace F) (f : ℝ →+* v.Completion) (y : ℝ) : IdeleGroup F where
  val := ((infComp v f y, 1) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
  inv := ((infComp v f (-y), 1) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
  val_inv := by
    change ((infComp v f y * infComp v f (-y), 1 * 1) :
      InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) = (1, 1)
    rw [← infComp_add, add_neg_cancel, infComp_zero, mul_one]
  inv_val := by
    change ((infComp v f (-y) * infComp v f y, 1 * 1) :
      InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) = (1, 1)
    rw [← infComp_add, neg_add_cancel, infComp_zero, mul_one]

theorem sv_add (v : InfinitePlace F) (f : ℝ →+* v.Completion) (a b : ℝ) :
    sv v f (a + b) = sv v f a * sv v f b := by
  apply Units.ext
  change ((infComp v f (a + b), 1) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) =
    ((infComp v f a * infComp v f b, 1 * 1) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
  rw [infComp_add, mul_one]

theorem sv_continuous (v : InfinitePlace F) (f : ℝ →+* v.Completion) (hf : Continuous f) :
    Continuous (sv v f) := by
  apply Units.continuous_iff.mpr
  constructor
  · change Continuous (fun y : ℝ ↦ ((infComp v f y, 1) :
      InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))
    exact (infComp_continuous v f hf).prodMk continuous_const
  · change Continuous (fun y : ℝ ↦ ((infComp v f (-y), 1) :
      InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))
    exact ((infComp_continuous v f hf).comp continuous_neg).prodMk continuous_const

theorem ideleNorm_sv (v : InfinitePlace F) (f : ℝ →+* v.Completion) (hf : ∀ x, ‖f x‖ = ‖x‖)
    (y : ℝ) : ideleNorm (sv v f y) = Real.exp y := by
  unfold ideleNorm
  have hfin : (∏ᶠ w : HeightOneSpectrum (𝓞 F), ‖((sv v f y : IdeleGroup F) :
      AdeleRing (𝓞 F) F).2 w‖) = 1 := by
    apply finprod_eq_one_of_forall_eq_one
    intro w
    change ‖(1 : FiniteAdeleRing (𝓞 F) F) w‖ = 1
    exact norm_one
  rw [hfin, mul_one]
  change (∏ w : InfinitePlace F, ‖infComp v f y w‖ ^ w.mult) = Real.exp y
  rw [Finset.prod_eq_single_of_mem v (Finset.mem_univ v)]
  · unfold infComp
    simp only [↓reduceDIte]
    rw [hf, Real.norm_of_nonneg (Real.exp_pos _).le, ← Real.exp_nat_mul]
    congr 1
    have : (v.mult : ℝ) ≠ 0 := by exact_mod_cast (InfinitePlace.mult_pos (w := v)).ne'
    field_simp
  · intro w _ hw
    unfold infComp
    simp only [dif_neg hw, norm_one, one_pow]

end Sigma

section InfRep

variable {F : Type*} [Field F] [NumberField F]

theorem mixedNorm_infiniteAdele (a : InfiniteAdeleRing F) :
    mixedEmbedding.norm (InfiniteAdeleRing.ringEquiv_mixedSpace F a) = ‖a‖ := by
  rw [InfiniteAdeleRing.norm_def, mixedEmbedding.norm_apply]
  congr 1
  funext w
  congr 1
  by_cases hw : w.IsReal
  · rw [mixedEmbedding.normAtPlace_apply_of_isReal hw]
    change ‖InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (a w)‖ = ‖a w‖
    exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero
      (map_zero _) (a w)
  · have hw' := InfinitePlace.not_isReal_iff_isComplex.mp hw
    rw [mixedEmbedding.normAtPlace_apply_of_isComplex hw']
    change ‖InfinitePlace.Completion.extensionEmbedding w (a w)‖ = ‖a w‖
    exact (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
      (map_zero _) (a w)

theorem exists_compact_infRep :
    ∃ K : Set (InfiniteAdeleRing F)ˣ, IsCompact K ∧
      ∀ a : (InfiniteAdeleRing F)ˣ, ‖a.val‖ = (1 : ℝ) →
        ∃ u : (𝓞 F)ˣ, Units.map (algebraMap (𝓞 F) (InfiniteAdeleRing F)).toMonoidHom u * a ∈ K := by
  classical
  let m := InfiniteAdeleRing.ringEquiv_mixedSpace F
  let h : InfiniteAdeleRing F ≃ₜ mixedEmbedding.mixedSpace F :=
    (Homeomorph.piEquivPiSubtypeProd InfinitePlace.IsReal
      (fun w : InfinitePlace F ↦ w.Completion)).trans
      (Homeomorph.prodCongr
        (Homeomorph.piCongrRight fun w ↦
          (InfinitePlace.Completion.isometryEquivRealOfIsReal w.2).toHomeomorph)
        ((Homeomorph.piCongrRight fun w ↦
          (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
            (InfinitePlace.not_isReal_iff_isComplex.mp w.2)).toHomeomorph).trans
          (Homeomorph.piCongrLeft (Y := fun _ ↦ ℂ)
            (Equiv.subtypeEquivRight fun _ ↦ InfinitePlace.not_isReal_iff_isComplex))))
  let S : Set (mixedEmbedding.mixedSpace F) :=
    closure (mixedEmbedding.fundamentalCone.normLeOne F) ∩ {z | mixedEmbedding.norm z = 1}
  have hc : IsCompact (closure (mixedEmbedding.fundamentalCone.normLeOne F)) :=
    (mixedEmbedding.fundamentalCone.isBounded_normLeOne F).isCompact_closure
  have hS : IsCompact S :=
    hc.inter_right (isClosed_eq (mixedEmbedding.continuous_norm F) continuous_const)
  let f := fun a : (InfiniteAdeleRing F)ˣ ↦ m a.val
  have hval : Topology.IsEmbedding (Units.val : (InfiniteAdeleRing F)ˣ → InfiniteAdeleRing F) :=
    (Units.isOpenEmbedding_val (R := (w : InfinitePlace F) → w.Completion)).isEmbedding
  have hf : Topology.IsInducing f := h.isInducing.comp hval.isInducing
  have hRange : S ⊆ Set.range f := by
    intro z hz
    have hnorm : ‖m.symm z‖ = (1 : ℝ) := by
      rw [← mixedNorm_infiniteAdele, RingEquiv.apply_symm_apply]
      exact hz.2
    have hu : IsUnit (m.symm z) := by
      by_contra hu
      rw [InfiniteAdeleRing.norm_eq_zero_of_not_isUnit hu] at hnorm
      exact zero_ne_one hnorm
    obtain ⟨a, ha⟩ := hu
    exact ⟨a, (congrArg m ha).trans (m.apply_symm_apply z)⟩
  refine ⟨f ⁻¹' S, hf.isCompact_preimage' hS hRange, fun a ha ↦ ?_⟩
  have hNorm : mixedEmbedding.norm (m a.val) = 1 :=
    (mixedNorm_infiniteAdele a.val).trans ha
  obtain ⟨u, hu⟩ := mixedEmbedding.fundamentalCone.exists_unit_smul_mem
    (hNorm.trans_ne one_ne_zero)
  have hm :
      f (Units.map (algebraMap (𝓞 F) (InfiniteAdeleRing F)).toMonoidHom u * a) = u • m a.val := by
    change m (algebraMap (𝓞 F) (InfiniteAdeleRing F) u.val * a.val) = _
    rw [map_mul, IsScalarTower.algebraMap_apply (𝓞 F) F (InfiniteAdeleRing F),
      ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp, mixedEmbedding.unitSMul_smul]
  have hn : mixedEmbedding.norm (u • m a.val) = 1 := by
    rw [mixedEmbedding.norm_unit_smul, hNorm]
  refine ⟨u, ?_⟩
  change f _ ∈ S
  rw [hm]
  exact ⟨subset_closure ⟨hu, hn.le⟩, hn⟩

end InfRep

section Ideals

variable {F : Type*} [Field F] [NumberField F]

open scoped nonZeroDivisors

theorem valued_eq_one_of_mem {v : HeightOneSpectrum (𝓞 F)} {x y : v.adicCompletion F}
    (hxy : x * y = 1) (hx : x ∈ v.adicCompletionIntegers F) (hy : y ∈ v.adicCompletionIntegers F) :
    Valued.v x = 1 := by
  have h1 : Valued.v x * Valued.v y = 1 := by rw [← map_mul, hxy, map_one]
  have hx' : Valued.v x ≤ 1 := hx
  have hy' : Valued.v y ≤ 1 := hy
  refine le_antisymm hx' ?_
  calc (1 : ℤᵐ⁰) = Valued.v x * Valued.v y := h1.symm
    _ ≤ Valued.v x * 1 := mul_le_mul' le_rfl hy'
    _ = Valued.v x := mul_one _

theorem fin_ne_zero (g : IdeleGroup F) (v : HeightOneSpectrum (𝓞 F)) :
    (g : AdeleRing (𝓞 F) F).2 v ≠ 0 := by
  intro h
  have := fin_mul_inv g v
  rw [h, zero_mul] at this
  exact zero_ne_one this

theorem eventually_valued_eq_one (g : IdeleGroup F) :
    ∀ᶠ v in cofinite, Valued.v ((g : AdeleRing (𝓞 F) F).2 v) = 1 := by
  filter_upwards [(g : AdeleRing (𝓞 F) F).2.2, ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2.2]
    with v h1 h2
  exact valued_eq_one_of_mem (fin_mul_inv g v) h1 h2

/-- The finite valuation of an idele. -/
noncomputable def ideleExponent (g : IdeleGroup F) (v : HeightOneSpectrum (𝓞 F)) : ℤ :=
  -WithZero.log (Valued.v ((g : AdeleRing (𝓞 F) F).2 v))

theorem eventually_ideleExponent_eq_zero (g : IdeleGroup F) :
    ∀ᶠ v in cofinite, ideleExponent g v = 0 :=
  (eventually_valued_eq_one g).mono fun v hv ↦ by simp [ideleExponent, hv]

/-- The prime of a finite place as a unit fractional ideal. -/
noncomputable def primeUnit (v : HeightOneSpectrum (𝓞 F)) : (FractionalIdeal (𝓞 F)⁰ F)ˣ :=
  Units.mk0 ((v.asIdeal : FractionalIdeal (𝓞 F)⁰ F))
    (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)

/-- The fractional ideal of an idele. -/
noncomputable def ideleFractionalIdeal : IdeleGroup F →* (FractionalIdeal (𝓞 F)⁰ F)ˣ where
  toFun g := ∏ᶠ v : HeightOneSpectrum (𝓞 F), (primeUnit v) ^ ideleExponent g v
  map_one' := by
    apply finprod_eq_one_of_forall_eq_one
    intro v
    change _ ^ (-WithZero.log (Valued.v (1 : v.adicCompletion F))) = _
    simp
  map_mul' g h := by
    let P (v : HeightOneSpectrum (𝓞 F)) : (FractionalIdeal (𝓞 F)⁰ F)ˣ := primeUnit v
    change (∏ᶠ v, P v ^ ideleExponent (g * h) v) =
      (∏ᶠ v, P v ^ ideleExponent g v) * (∏ᶠ v, P v ^ ideleExponent h v)
    have hs (a : IdeleGroup F) :
        (Function.mulSupport fun v ↦ P v ^ ideleExponent a v).Finite :=
      eventually_cofinite.mp ((eventually_ideleExponent_eq_zero a).mono
        fun v hv ↦ by simp [hv])
    rw [← finprod_mul_distrib (hs g) (hs h)]
    apply finprod_congr
    intro v
    rw [← zpow_add]
    congr 1
    change -WithZero.log (Valued.v ((g : AdeleRing (𝓞 F) F).2 v * (h : AdeleRing (𝓞 F) F).2 v)) =
      -WithZero.log (Valued.v ((g : AdeleRing (𝓞 F) F).2 v)) +
        -WithZero.log (Valued.v ((h : AdeleRing (𝓞 F) F).2 v))
    rw [map_mul, WithZero.log_mul, neg_add]
    · exact (Valuation.ne_zero_iff _).mpr (fin_ne_zero g v)
    · exact (Valuation.ne_zero_iff _).mpr (fin_ne_zero h v)

theorem coe_ideleFractionalIdeal (g : IdeleGroup F) :
    (ideleFractionalIdeal g : FractionalIdeal (𝓞 F)⁰ F) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 F),
        (v.asIdeal : FractionalIdeal (𝓞 F)⁰ F) ^ ideleExponent g v := by
  change Units.coeHom _ (∏ᶠ v : HeightOneSpectrum (𝓞 F), (primeUnit v) ^ ideleExponent g v) = _
  rw [map_finprod]
  · apply finprod_congr
    intro v
    exact Units.val_zpow_eq_zpow_val (primeUnit v) _
  · exact eventually_cofinite.mp ((eventually_ideleExponent_eq_zero g).mono
      fun v hv ↦ by simp [hv])

theorem ideleFractionalIdeal_principal (x : Fˣ) :
    ideleFractionalIdeal (principalIdele F x) = toPrincipalIdeal (𝓞 F) F x := by
  obtain ⟨n, d, hnd⟩ := IsLocalization.exists_mk'_eq (𝓞 F)⁰ (x : F)
  have hn : n ≠ 0 := by
    rintro rfl
    exact x.ne_zero (by rw [← hnd, IsFractionRing.mk'_eq_div, map_zero, zero_div])
  apply Units.ext
  rw [coe_ideleFractionalIdeal, coe_toPrincipalIdeal, ← hnd,
    ← FractionalIdeal.finprod_heightOneSpectrum_factorization_principal_fraction (K := F) hn d]
  apply finprod_congr
  intro v
  congr 1
  change -WithZero.log (Valued.v ((x : F) : v.adicCompletion F)) = _
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', ← hnd,
    HeightOneSpectrum.valuation_of_mk', v.intValuation_if_neg hn,
    v.intValuation_if_neg (nonZeroDivisors.coe_ne_zero d), WithZero.log_div,
    WithZero.log_exp, WithZero.log_exp]
  · ring
  · exact WithZero.exp_ne_zero
  · exact WithZero.exp_ne_zero

theorem exists_integral_fin_idele (g : IdeleGroup F)
    (hg : ClassGroup.mk F (ideleFractionalIdeal g) = 1) :
    ∃ x : Fˣ, ∀ v : HeightOneSpectrum (𝓞 F),
      Valued.v (((g / principalIdele F x : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v) = 1 := by
  obtain ⟨x, hx⟩ := (ClassGroup.mk_eq_one_iff.mp hg).principal
  have hx' : (ideleFractionalIdeal g : FractionalIdeal (𝓞 F)⁰ F) =
      FractionalIdeal.spanSingleton _ x := by
    rwa [← FractionalIdeal.coeToSubmodule_inj, FractionalIdeal.coe_spanSingleton]
  have hx0 : x ≠ 0 := fun h ↦ (ideleFractionalIdeal g).ne_zero
    (hx'.trans (FractionalIdeal.spanSingleton_eq_zero_iff.mpr h))
  let u := Units.mk0 x hx0
  have hI : ideleFractionalIdeal (g / principalIdele F u) = 1 := by
    rw [map_div, ideleFractionalIdeal_principal, div_eq_one]
    apply Units.ext
    rw [coe_toPrincipalIdeal]
    exact hx'
  refine ⟨u, fun v ↦ ?_⟩
  let a := g / principalIdele F u
  have hc := FractionalIdeal.count_finprod F v (ideleExponent a)
    (eventually_ideleExponent_eq_zero a)
  rw [← coe_ideleFractionalIdeal, hI, Units.val_one, FractionalIdeal.count_one] at hc
  have hv : WithZero.log (Valued.v ((a : AdeleRing (𝓞 F) F).2 v)) = 0 := neg_eq_zero.mp hc.symm
  have hv0 : Valued.v ((a : AdeleRing (𝓞 F) F).2 v) ≠ (0 : ℤᵐ⁰) :=
    (Valuation.ne_zero_iff _).mpr (fin_ne_zero a v)
  change Valued.v ((a : AdeleRing (𝓞 F) F).2 v) = (1 : ℤᵐ⁰)
  rw [← WithZero.exp_log hv0, hv, WithZero.exp_zero]

end Ideals

section CompactBox

variable {F : Type*} [Field F] [NumberField F]

/-- The finite adele with coordinates given by local integral units. -/
noncomputable def boxVal (u : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletionIntegers F)ˣ) :
    FiniteAdeleRing (𝓞 F) F :=
  (⟨fun v ↦ ((u v : v.adicCompletionIntegers F) : v.adicCompletion F),
    Filter.Eventually.of_forall fun v ↦ (u v : v.adicCompletionIntegers F).2⟩ :
    Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F])

theorem boxVal_mul_inv (u : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletionIntegers F)ˣ) :
    boxVal u * boxVal u⁻¹ = 1 := by
  apply RestrictedProduct.ext
  intro v
  change ((u v : v.adicCompletionIntegers F) : v.adicCompletion F) *
    (((u v)⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) = 1
  rw [← Subring.coe_mul, Units.mul_inv]
  rfl

theorem boxVal_continuous : Continuous (boxVal (F := F)) := by
  apply continuous_rp_of_uniform
  · intro v
    exact continuous_subtype_val.comp (Units.continuous_val.comp (continuous_apply v))
  · exact Filter.Eventually.of_forall fun v u ↦ (u v : v.adicCompletionIntegers F).2

/-- An idele from an Archimedean unit and a tuple of local integral units. -/
noncomputable def boxIdele (p : (InfiniteAdeleRing F)ˣ × ((v : HeightOneSpectrum (𝓞 F)) →
    (v.adicCompletionIntegers F)ˣ)) : IdeleGroup F where
  val := ((p.1.val, boxVal p.2) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
  inv := ((p.1⁻¹.val, boxVal p.2⁻¹) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
  val_inv := by
    change ((p.1.val * p.1⁻¹.val, boxVal p.2 * boxVal p.2⁻¹) :
      InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) = (1, 1)
    rw [boxVal_mul_inv, Units.mul_inv]
  inv_val := by
    change ((p.1⁻¹.val * p.1.val, boxVal p.2⁻¹ * boxVal p.2) :
      InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) = (1, 1)
    have := boxVal_mul_inv p.2⁻¹
    rw [inv_inv] at this
    rw [this, Units.inv_mul]

theorem boxIdele_continuous : Continuous (boxIdele (F := F)) := by
  apply Units.continuous_iff.mpr
  constructor
  · change Continuous (fun p : (InfiniteAdeleRing F)ˣ × ((v : HeightOneSpectrum (𝓞 F)) →
      (v.adicCompletionIntegers F)ˣ) ↦ ((p.1.val, boxVal p.2) :
        InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))
    exact (Units.continuous_val.comp continuous_fst).prodMk (boxVal_continuous.comp continuous_snd)
  · change Continuous (fun p : (InfiniteAdeleRing F)ˣ × ((v : HeightOneSpectrum (𝓞 F)) →
      (v.adicCompletionIntegers F)ˣ) ↦ ((p.1⁻¹.val, boxVal p.2⁻¹) :
        InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))
    exact (Units.continuous_coe_inv.comp continuous_fst).prodMk
      (boxVal_continuous.comp (continuous_inv.comp continuous_snd))

theorem isCompact_boxImage {A : Set (InfiniteAdeleRing F)ˣ} (hA : IsCompact A) :
    IsCompact (boxIdele '' (A ×ˢ (Set.univ : Set ((v : HeightOneSpectrum (𝓞 F)) →
      (v.adicCompletionIntegers F)ˣ)))) := by
  have : ∀ v : HeightOneSpectrum (𝓞 F), CompactSpace (v.adicCompletionIntegers F) :=
    fun v ↦ compactSpace_adicCompletionIntegers v
  exact (hA.prod isCompact_univ).image boxIdele_continuous

/-- The Archimedean part of an idele. -/
noncomputable def atInf : IdeleGroup F →* (InfiniteAdeleRing F)ˣ :=
  Units.map ((RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F) :
    AdeleRing (𝓞 F) F →+* InfiniteAdeleRing F)).toMonoidHom

theorem mem_boxImage {A : Set (InfiniteAdeleRing F)ˣ} (z : IdeleGroup F) (hzA : atInf z ∈ A)
    (hz : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v ((z : AdeleRing (𝓞 F) F).2 v) = 1) :
    z ∈ boxIdele '' (A ×ˢ (Set.univ : Set ((v : HeightOneSpectrum (𝓞 F)) →
      (v.adicCompletionIntegers F)ˣ))) := by
  have hzi : ∀ v : HeightOneSpectrum (𝓞 F),
      Valued.v (((z⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v) = 1 := by
    intro v
    have h1 := fin_mul_inv z v
    have h2 : Valued.v ((z : AdeleRing (𝓞 F) F).2 v) *
        Valued.v (((z⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v) = 1 := by
      rw [← map_mul, h1, map_one]
    rw [hz v, one_mul] at h2
    exact h2
  let u : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletionIntegers F)ˣ := fun v ↦
    { val := ⟨(z : AdeleRing (𝓞 F) F).2 v, (hz v).le⟩
      inv := ⟨((z⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v, (hzi v).le⟩
      val_inv := Subtype.ext (fin_mul_inv z v)
      inv_val := Subtype.ext (by rw [mul_comm]; exact fin_mul_inv z v) }
  refine ⟨(atInf z, u), ⟨hzA, Set.mem_univ _⟩, ?_⟩
  apply Units.ext
  rfl

end CompactBox

section NormOne

variable {F : Type*} [Field F] [NumberField F]

theorem norm_eq_one_of_valued {v : HeightOneSpectrum (𝓞 F)} {x : v.adicCompletion F}
    (hx : Valued.v x = 1) : ‖x‖ = 1 := by
  rw [FinitePlace.norm_def, hx, map_one, NNReal.coe_one]

theorem ideleNorm_principal_inv_mul (g : IdeleGroup F) (x : Fˣ) :
    ideleNorm (g / principalIdele F x) = ideleNorm g := by
  rw [div_eq_mul_inv, ideleNorm_mul, ← map_inv, ideleNorm_principal, mul_one]

theorem ideleNorm_principal_mul (g : IdeleGroup F) (x : Fˣ) :
    ideleNorm (principalIdele F x * g) = ideleNorm g := by
  rw [ideleNorm_mul, ideleNorm_principal, one_mul]

theorem global_unit_valuation (u : (𝓞 F)ˣ) (v : HeightOneSpectrum (𝓞 F)) :
    v.valuation F ((Units.map (algebraMap (𝓞 F) F).toMonoidHom u : Fˣ) : F) = 1 := by
  let uF := Units.map (algebraMap (𝓞 F) F).toMonoidHom u
  have hmul : v.valuation F (uF : F) * v.valuation F (↑uF⁻¹ : F) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  apply le_antisymm (v.valuation_le_one u.val)
  calc
    1 = v.valuation F (uF : F) * v.valuation F (↑uF⁻¹ : F) := hmul.symm
    _ ≤ v.valuation F (uF : F) * 1 := by
      gcongr
      exact v.valuation_le_one (u⁻¹ : (𝓞 F)ˣ).val
    _ = v.valuation F (uF : F) := mul_one _

theorem exists_small_rep {A : Set (InfiniteAdeleRing F)ˣ}
    (hRep : ∀ a : (InfiniteAdeleRing F)ˣ, ‖a.val‖ = (1 : ℝ) →
        ∃ u : (𝓞 F)ˣ, Units.map (algebraMap (𝓞 F) (InfiniteAdeleRing F)).toMonoidHom u * a ∈ A)
    (g : IdeleGroup F) (hg1 : ideleNorm g = 1)
    (hgf : ClassGroup.mk F (ideleFractionalIdeal g) = 1) :
    ∃ z ∈ boxIdele '' (A ×ˢ (Set.univ : Set ((v : HeightOneSpectrum (𝓞 F)) →
      (v.adicCompletionIntegers F)ˣ))),
      ideleNorm z = 1 ∧ (QuotientGroup.mk z : IdeleClassGroup F) = QuotientGroup.mk g := by
  obtain ⟨x, hx⟩ := exists_integral_fin_idele g hgf
  let y : IdeleGroup F := g / principalIdele F x
  have hy1 : ideleNorm y = 1 := by rw [ideleNorm_principal_inv_mul, hg1]
  have hFin : (∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(y : AdeleRing (𝓞 F) F).2 v‖) = 1 :=
    finprod_eq_one_of_forall_eq_one fun v ↦ norm_eq_one_of_valued (hx v)
  have hInf : ‖(atInf y).val‖ = (1 : ℝ) := by
    have hn : ideleNorm y = (∏ w : InfinitePlace F, ‖(y : AdeleRing (𝓞 F) F).1 w‖ ^ w.mult) *
        ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(y : AdeleRing (𝓞 F) F).2 v‖ := rfl
    rw [hy1, hFin, mul_one] at hn
    rw [InfiniteAdeleRing.norm_def]
    exact hn.symm
  obtain ⟨u, hu⟩ := hRep (atInf y) hInf
  let uF : Fˣ := Units.map (algebraMap (𝓞 F) F).toMonoidHom u
  let z : IdeleGroup F := principalIdele F uF * y
  have hArch : atInf z =
      Units.map (algebraMap (𝓞 F) (InfiniteAdeleRing F)).toMonoidHom u * atInf y := by
    apply Units.ext
    change algebraMap F (InfiniteAdeleRing F) (algebraMap (𝓞 F) F u.val) * _ =
      algebraMap (𝓞 F) (InfiniteAdeleRing F) u.val * _
    rw [← IsScalarTower.algebraMap_apply]
    rfl
  refine ⟨z, mem_boxImage z (by rw [hArch]; exact hu) ?_, ?_, ?_⟩
  · intro v
    change Valued.v (((uF : F) : v.adicCompletion F) * (y : AdeleRing (𝓞 F) F).2 v) = 1
    rw [map_mul, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', global_unit_valuation,
      one_mul]
    exact hx v
  · rw [ideleNorm_principal_mul]
    exact hy1
  · have h1 : (QuotientGroup.mk (principalIdele F uF) : IdeleClassGroup F) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ⟨uF, rfl⟩
    have h2 : (QuotientGroup.mk (principalIdele F x) : IdeleClassGroup F) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ⟨x, rfl⟩
    change (QuotientGroup.mk (principalIdele F uF * (g / principalIdele F x)) :
      IdeleClassGroup F) = QuotientGroup.mk g
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_div, h1, h2, div_one]
    exact one_mul (QuotientGroup.mk g : IdeleGroup F ⧸ principalIdeles F)

theorem isCompact_normOne :
    IsCompact ((QuotientGroup.mk : IdeleGroup F → IdeleClassGroup F) ''
      {g | ideleNorm g = 1}) := by
  classical
  obtain ⟨A, hA, hRep⟩ := exists_compact_infRep (F := F)
  let K := boxIdele '' (A ×ˢ (Set.univ : Set ((v : HeightOneSpectrum (𝓞 F)) →
      (v.adicCompletionIntegers F)ˣ)))
  have hK : IsCompact K := isCompact_boxImage hA
  let J1 : Set (IdeleGroup F) := {g | ideleNorm g = 1}
  have hJ1 : IsClosed J1 := isClosed_singleton.preimage ideleNorm_continuous
  have hKJ : IsCompact (K ∩ J1) := hK.inter_right hJ1
  let f := (ClassGroup.mk F).comp (ideleFractionalIdeal (F := F))
  let I := Set.range (fun g : J1 ↦ f g.val)
  let r (c : I) : J1 := Classical.choose c.property
  have hr (c : I) : f (r c).val = c.val := Classical.choose_spec c.property
  let U (c : I) := (fun t ↦ (QuotientGroup.mk ((r c).val * t) : IdeleClassGroup F)) '' (K ∩ J1)
  have hU (c : I) : IsCompact (U c) :=
    hKJ.image (QuotientGroup.continuous_mk.comp (continuous_const.mul continuous_id))
  have hfin : Finite I := Subtype.finite
  have heq : (QuotientGroup.mk : IdeleGroup F → IdeleClassGroup F) '' J1 = ⋃ c, U c := by
    apply Set.Subset.antisymm
    · rintro _ ⟨g, hg, rfl⟩
      let c : I := ⟨f g, ⟨⟨g, hg⟩, rfl⟩⟩
      have hgr1 : ideleNorm (g / (r c).val) = 1 := by
        rw [div_eq_mul_inv, ideleNorm_mul]
        have h1 : ideleNorm (r c).val = 1 := (r c).2
        have h2 : ideleNorm ((r c).val⁻¹) = 1 := by
          have := ideleNorm_mul (r c).val ((r c).val⁻¹)
          rw [mul_inv_cancel, h1, one_mul] at this
          have h3 : ideleNorm (1 : IdeleGroup F) = 1 := by
            have := ideleNorm_mul (1 : IdeleGroup F) 1
            rw [mul_one] at this
            have hp := ideleNorm_pos (1 : IdeleGroup F)
            field_simp at this
            linarith
          rw [h3] at this
          exact this.symm
        rw [show ideleNorm g = 1 from hg, h2, one_mul]
      have hgrf : ClassGroup.mk F (ideleFractionalIdeal (g / (r c).val)) = 1 := by
        change f (g / (r c).val) = 1
        rw [map_div, hr, div_self']
      obtain ⟨y, hy, hy1, hyq⟩ := exists_small_rep hRep (g / (r c).val) hgr1 hgrf
      refine Set.mem_iUnion.mpr ⟨c, y, ⟨hy, hy1⟩, ?_⟩
      change (QuotientGroup.mk ((r c).val * y) : IdeleClassGroup F) = QuotientGroup.mk g
      rw [QuotientGroup.mk_mul, hyq, QuotientGroup.mk_div]
      exact mul_div_cancel (QuotientGroup.mk (r c).val : IdeleGroup F ⧸ principalIdeles F)
        (QuotientGroup.mk g : IdeleGroup F ⧸ principalIdeles F)
    · intro a ha
      obtain ⟨c, hc⟩ := Set.mem_iUnion.mp ha
      obtain ⟨t, ⟨_, ht⟩, rfl⟩ := hc
      refine ⟨(r c).val * t, ?_, rfl⟩
      change ideleNorm ((r c).val * t) = 1
      rw [ideleNorm_mul, show ideleNorm (r c).val = 1 from (r c).2,
        show ideleNorm t = 1 from ht, one_mul]
  change IsCompact ((QuotientGroup.mk : IdeleGroup F → IdeleClassGroup F) '' J1)
  rw [heq]
  exact isCompact_iUnion hU

end NormOne

section SUnitRank

variable {F : Type*} [Field F] [NumberField F]

open scoped Classical nonZeroDivisors in
theorem exists_prime_power_generator (v : HeightOneSpectrum (𝓞 F)) :
    ∃ x : Fˣ, ∀ w : HeightOneSpectrum (𝓞 F),
      w.valuation F (x : F) = if w = v then WithZero.exp (-(classNumber F : ℤ)) else 1 := by
  classical
  let n := classNumber F
  have hv : v.asIdeal ∈ (Ideal (𝓞 F))⁰ := mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot
  have hpow : (ClassGroup.mk0 ⟨v.asIdeal, hv⟩) ^ n = 1 := pow_card_eq_one
  have hp : (v.asIdeal ^ n).IsPrincipal := by
    rw [← ClassGroup.mk0_eq_one_iff (pow_mem hv n), ← hpow, ← map_pow]
    rfl
  obtain ⟨a, ha⟩ := hp
  change v.asIdeal ^ n = Ideal.span {a} at ha
  have ha₀ : a ≠ 0 := by
    rintro rfl
    exact (pow_ne_zero n v.ne_bot) (by simpa using ha)
  have haF : algebraMap (𝓞 F) F a ≠ 0 := fun h ↦
    ha₀ (IsFractionRing.injective (𝓞 F) F (h.trans (map_zero _).symm))
  refine ⟨Units.mk0 _ haF, fun w ↦ ?_⟩
  change w.valuation F (algebraMap (𝓞 F) F a) = _
  rw [w.valuation_of_algebraMap]
  by_cases h : w = v
  · subst w
    rw [if_pos rfl, v.intValuation_eq_exp_neg_multiplicity ha₀]
    have hmult : multiplicity v.asIdeal (Ideal.span {a}) = n := by
      rw [← ha]
      refine multiplicity_eq_of_dvd_of_not_dvd dvd_rfl ?_
      rw [pow_dvd_pow_iff v.ne_bot (mt Ideal.isUnit_iff.mp v.isPrime.ne_top)]
      exact Nat.not_succ_le_self n
    rw [hmult]
  · rw [if_neg h, w.intValuation_eq_one_iff]
    intro hd
    have hw : w.asIdeal ∣ v.asIdeal ^ n := ha.symm ▸ (Ideal.dvd_span_singleton.mpr hd)
    have hle : v.asIdeal ≤ w.asIdeal :=
      w.isPrime.le_of_pow_le (Ideal.dvd_iff_le.mp hw)
    exact h (HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top hle).symm)

theorem sUnits_finiteness (Sf : Finset (HeightOneSpectrum (𝓞 F))) :
    Group.FG (SUnits Sf) ∧ Module.finrank ℤ (Additive (SUnits Sf)) =
      Fintype.card (InfinitePlace F) + Sf.card - 1 := by
  classical
  let i : (𝓞 F)ˣ →* SUnits Sf := (Units.map (algebraMap (𝓞 F) F).toMonoidHom).codRestrict
    (SUnits Sf) (fun u v _ ↦ global_unit_valuation u v)
  let d : SUnits Sf →* Fˣ := (SUnits Sf).subtype
  let f := i.toAdditive.toIntLinearMap
  let ord : Additive (SUnits Sf) →ₗ[ℤ] (Sf → ℤ) :=
    LinearMap.pi fun v ↦ ((v.val.valuationOfNeZero : Fˣ →* Multiplicative ℤ).comp d)
      |>.toAdditive |>.toIntLinearMap
  have hfi : Function.Injective f := by
    intro x y h
    have h' := congrArg (fun a : Additive (SUnits Sf) ↦ ((a.toMul : Fˣ) : F)) h
    apply Additive.toMul.injective
    apply Units.ext
    exact IsFractionRing.injective (𝓞 F) F h'
  have hval (u : SUnits Sf) (v : Sf) :
      WithZero.exp (ord (.ofMul u) v) = v.val.valuation F ((u : Fˣ) : F) :=
    v.val.valuationOfNeZero_eq (d u)
  have hexact : Function.Exact f ord := by
    intro a
    change ord a = 0 ↔ ∃ b : Additive (𝓞 F)ˣ, i b.toMul = a.toMul
    constructor
    · intro h
      let u := a.toMul
      have hu (v : HeightOneSpectrum (𝓞 F)) : v.valuation F ((u : Fˣ) : F) = 1 := by
        by_cases hv : v ∈ Sf
        · have hu := hval u ⟨v, hv⟩
          change WithZero.exp (ord a _) = _ at hu
          simpa [h] using hu.symm
        · exact u.property v hv
      obtain ⟨x, hx⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F ((u : Fˣ) : F)
        (fun v ↦ (hu v).le)
      obtain ⟨y, hy⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F
        (((u : Fˣ)⁻¹ : Fˣ) : F) (fun v ↦ by rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one])
      have hxy : x * y = 1 := (IsFractionRing.injective (𝓞 F) F) (by
        rw [map_mul, hx, hy, map_one]
        exact (u : Fˣ).mul_inv)
      let b : (𝓞 F)ˣ := ⟨x, y, hxy, (mul_comm y x).trans hxy⟩
      refine ⟨.ofMul b, ?_⟩
      apply Subtype.ext
      apply Units.ext
      exact hx
    · rintro ⟨b, hb⟩
      have hfb : f b = a := hb
      rw [← hfb]
      funext v
      apply WithZero.exp_inj.mp
      change WithZero.exp (ord (.ofMul (i b.toMul)) v) = WithZero.exp ((0 : Sf → ℤ) v)
      rw [hval, Pi.zero_apply, WithZero.exp_zero]
      exact global_unit_valuation b.toMul v.val
  have hrange : Module.finrank ℤ (LinearMap.range ord) = Sf.card := by
    let n : ℤ := classNumber F
    have hn : n ≠ 0 := Int.natCast_ne_zero.mpr (classNumber_ne_zero F)
    let m : (Sf → ℤ) →ₗ[ℤ] (Sf → ℤ) := DistribSMul.toLinearMap ℤ _ (-n)
    have hm : Function.Injective m := fun x y h ↦ funext fun v ↦ by
      have hv : -n * x v = -n * y v := congrFun h v
      exact mul_left_cancel₀ (neg_ne_zero.mpr hn) hv
    have hsingle (v : Sf) : Pi.single v (-n) ∈ LinearMap.range ord := by
      obtain ⟨x, hx⟩ := exists_prime_power_generator v.val
      let u : SUnits Sf := ⟨x, fun w hw ↦ by
        rw [hx, if_neg (show w ≠ v.val from fun e ↦ hw (e.symm ▸ v.property))]⟩
      refine ⟨.ofMul u, ?_⟩
      funext w
      apply WithZero.exp_inj.mp
      rw [hval]
      change w.val.valuation F (x : F) = _
      rw [hx]
      by_cases h : w = v
      · subst w
        simp [n]
      · rw [if_neg (fun e ↦ h (Subtype.ext e)), Pi.single_eq_of_ne h, WithZero.exp_zero]
    have hle : LinearMap.range m ≤ LinearMap.range ord := by
      rintro _ ⟨x, rfl⟩
      rw [show m x = ∑ v : Sf, x v • Pi.single v (-n) from by
        funext w
        simp [m, Finset.sum_apply, Pi.single_apply, mul_comm]]
      exact Submodule.sum_mem _ fun v _ ↦ Submodule.smul_mem _ _ (hsingle v)
    have hcard : Module.finrank ℤ (Sf → ℤ) = Sf.card := by
      simp
    apply le_antisymm ((Submodule.finrank_le _).trans_eq hcard)
    rw [← hcard, ← LinearMap.finrank_range_of_inj hm]
    exact Submodule.finrank_mono hle
  have hk : LinearMap.ker ord = LinearMap.range f := hexact.linearMap_ker_eq
  have : Module.Finite ℤ (LinearMap.ker ord) :=
    hk ▸ inferInstanceAs (Module.Finite ℤ (LinearMap.range f))
  have : Module.Finite ℤ (_ ⧸ LinearMap.ker ord) := Module.Finite.equiv ord.quotKerEquivRange.symm
  have : Module.Finite ℤ (Additive (SUnits Sf)) :=
    Module.Finite.of_submodule_quotient (LinearMap.ker ord)
  have hr := (LinearMap.ker ord).finrank_quotient_add_finrank
  rw [ord.quotKerEquivRange.finrank_eq, hk, LinearMap.finrank_range_of_inj hfi,
    NumberField.Units.finrank_eq, NumberField.Units.rank, hrange] at hr
  have hfg : AddGroup.FG (Additive (SUnits Sf)) :=
    Module.Finite.iff_addGroup_fg.mp inferInstance
  refine ⟨AddGroup.fg_iff_mul_fg.mp hfg, ?_⟩
  have hpos : 0 < Fintype.card (InfinitePlace F) := Fintype.card_pos
  omega

end SUnitRank

section SClassGroup

variable {F : Type*} [Field F] [NumberField F]

open scoped nonZeroDivisors

theorem exists_den (Sf : Finset (HeightOneSpectrum (𝓞 F))) (z : F)
    (hz : ∀ w : HeightOneSpectrum (𝓞 F), w ∉ Sf → w.valuation F z ≤ 1) :
    ∃ s : 𝓞 F, s ≠ 0 ∧ (∀ w : HeightOneSpectrum (𝓞 F), w ∉ Sf → w.intValuation s = 1) ∧
      ∀ w : HeightOneSpectrum (𝓞 F), w.valuation F (algebraMap (𝓞 F) F s * z) ≤ 1 := by
  classical
  by_cases hz0 : z = 0
  · refine ⟨1, one_ne_zero, fun w _ ↦ by simp, fun w ↦ ?_⟩
    rw [hz0, mul_zero, map_zero]
    exact zero_le
  let π : HeightOneSpectrum (𝓞 F) → Fˣ := fun v ↦ (exists_prime_power_generator v).choose
  have hπ : ∀ v w : HeightOneSpectrum (𝓞 F), w.valuation F (π v : F) =
      if w = v then WithZero.exp (-(classNumber F : ℤ)) else 1 :=
    fun v ↦ (exists_prime_power_generator v).choose_spec
  let N : ℕ := ∑ v ∈ Sf, (WithZero.log (v.valuation F z)).toNat
  let t : Fˣ := ∏ v ∈ Sf, π v ^ N
  have ht : ∀ w : HeightOneSpectrum (𝓞 F), w.valuation F (t : F) =
      if w ∈ Sf then WithZero.exp (-(classNumber F : ℤ)) ^ N else 1 := by
    intro w
    have : (t : F) = ∏ v ∈ Sf, (π v : F) ^ N := by
      simp only [t, Units.coe_prod, Units.val_pow_eq_pow_val]
    rw [this, map_prod]
    simp only [map_pow, hπ]
    have e : ∀ v ∈ Sf, (if w = v then WithZero.exp (-(classNumber F : ℤ)) else 1) ^ N =
        if w = v then WithZero.exp (-(classNumber F : ℤ)) ^ N else 1 := by
      intro v _
      split_ifs <;> simp
    rw [Finset.prod_congr rfl e, Finset.prod_ite_eq]
  have htle : ∀ w : HeightOneSpectrum (𝓞 F), w.valuation F (t : F) ≤ 1 := by
    intro w
    rw [ht w]
    split_ifs
    · rw [← WithZero.exp_nsmul, ← WithZero.exp_zero, WithZero.exp_le_exp]
      have : (0 : ℤ) ≤ (classNumber F : ℤ) := Int.natCast_nonneg _
      have h2 : (0 : ℤ) ≤ (N : ℤ) := Int.natCast_nonneg _
      rw [nsmul_eq_mul]
      nlinarith
    · exact le_rfl
  obtain ⟨s, hs⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F (t : F) htle
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [map_zero] at hs
    exact t.ne_zero hs.symm
  refine ⟨s, hs0, fun w hw ↦ ?_, fun w ↦ ?_⟩
  · rw [← HeightOneSpectrum.valuation_of_algebraMap (K := F)]
    change w.valuation F (algebraMap (𝓞 F) F s) = 1
    rw [hs, ht w, if_neg hw]
  · rw [hs, map_mul, ht w]
    split_ifs with hw
    · have hzw : w.valuation F z ≠ 0 := (Valuation.ne_zero_iff _).mpr hz0
      rw [← WithZero.exp_log hzw, ← WithZero.exp_nsmul, ← WithZero.exp_add, ← WithZero.exp_zero,
        WithZero.exp_le_exp, nsmul_eq_mul]
      have hle : WithZero.log (w.valuation F z) ≤ (N : ℤ) := by
        have h1 : WithZero.log (w.valuation F z) ≤ ((WithZero.log (w.valuation F z)).toNat : ℤ) :=
          Int.self_le_toNat _
        have h2 : (WithZero.log (w.valuation F z)).toNat ≤ N :=
          Finset.single_le_sum (f := fun v ↦ (WithZero.log (v.valuation F z)).toNat)
            (fun _ _ ↦ Nat.zero_le _) hw
        omega
      have hh : (1 : ℤ) ≤ (classNumber F : ℤ) := by
        have := NumberField.classNumber_ne_zero F
        omega
      have h2 : (0 : ℤ) ≤ (N : ℤ) := Int.natCast_nonneg _
      nlinarith
    · rw [one_mul]
      exact hz w hw

/-- The multiplicative set of integers which are units outside `S`. -/
def sDen (Sf : Finset (HeightOneSpectrum (𝓞 F))) : Submonoid (𝓞 F) where
  carrier := {s | s ≠ 0 ∧ ∀ w : HeightOneSpectrum (𝓞 F), w ∉ Sf → w.intValuation s = 1}
  mul_mem' := by
    intro a b ha hb
    exact ⟨mul_ne_zero ha.1 hb.1, fun w hw ↦ by rw [map_mul, ha.2 w hw, hb.2 w hw, one_mul]⟩
  one_mem' := ⟨one_ne_zero, fun w _ ↦ map_one _⟩

theorem sDen_le (Sf : Finset (HeightOneSpectrum (𝓞 F))) : sDen Sf ≤ (𝓞 F)⁰ :=
  fun _ hs ↦ mem_nonZeroDivisors_of_ne_zero hs.1

instance isLocalization_sIntegers (Sf : Finset (HeightOneSpectrum (𝓞 F))) :
    IsLocalization (sDen Sf) (SIntegers Sf) where
  map_units := by
    rintro ⟨s, hs0, hs⟩
    have hsF : algebraMap (𝓞 F) F s ≠ 0 := fun h ↦
      hs0 (IsFractionRing.injective (𝓞 F) F (h.trans (map_zero _).symm))
    have hinv : (algebraMap (𝓞 F) F s)⁻¹ ∈ SIntegers Sf := by
      intro w hw
      rw [map_inv₀, HeightOneSpectrum.valuation_of_algebraMap, hs w hw, inv_one]
    refine ⟨⟨algebraMap (𝓞 F) (SIntegers Sf) s, ⟨_, hinv⟩, ?_, ?_⟩, rfl⟩
    · apply Subtype.ext
      change algebraMap (𝓞 F) F s * (algebraMap (𝓞 F) F s)⁻¹ = 1
      exact mul_inv_cancel₀ hsF
    · apply Subtype.ext
      change (algebraMap (𝓞 F) F s)⁻¹ * algebraMap (𝓞 F) F s = 1
      exact inv_mul_cancel₀ hsF
  surj := by
    intro z
    obtain ⟨s, hs0, hs, hsz⟩ := exists_den Sf (z : F) (fun w hw ↦ z.2 w hw)
    obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F _ hsz
    refine ⟨⟨a, ⟨s, hs0, hs⟩⟩, ?_⟩
    apply Subtype.ext
    change (z : F) * algebraMap (𝓞 F) F s = algebraMap (𝓞 F) F a
    rw [ha, mul_comm]
  exists_of_eq := by
    intro x y h
    refine ⟨1, ?_⟩
    have h' : algebraMap (𝓞 F) F x = algebraMap (𝓞 F) F y :=
      congrArg (fun a : SIntegers Sf ↦ (a : F)) h
    rw [IsFractionRing.injective (𝓞 F) F h']

theorem isDedekindDomain_sIntegers (Sf : Finset (HeightOneSpectrum (𝓞 F))) :
    IsDedekindDomain (SIntegers Sf) :=
  IsLocalization.isDedekindDomain (𝓞 F) (sDen_le Sf) (SIntegers Sf)

theorem finite_classGroup_sIntegers (Sf : Finset (HeightOneSpectrum (𝓞 F))) :
    Finite (ClassGroup (SIntegers Sf)) := by
  have := isDedekindDomain_sIntegers Sf
  apply Finite.of_surjective (ClassGroup.extendedHom (𝓞 F) (SIntegers Sf))
  intro c
  obtain ⟨J, rfl⟩ := ClassGroup.mk0_surjective c
  let I : Ideal (𝓞 F) := J.val.under (𝓞 F)
  have hmap : I.map (algebraMap (𝓞 F) (SIntegers Sf)) = J.val :=
    IsLocalization.map_under (sDen Sf) (SIntegers Sf) J.val
  have hI : I ≠ ⊥ := by
    intro he
    rw [he, Ideal.map_bot] at hmap
    exact (nonZeroDivisors.ne_zero J.property) hmap.symm
  refine ⟨ClassGroup.mk0 ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩, ?_⟩
  rw [ClassGroup.extendedHom_mk0]
  congr 1
  exact Subtype.ext hmap

end SClassGroup

section SCompact

variable {F : Type*} [Field F] [NumberField F]

theorem valued_eq_one_iff (g : IdeleGroup F) (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v ((g : AdeleRing (𝓞 F) F).2 v) = 1 ↔
      (g : AdeleRing (𝓞 F) F).2 v ∈ v.adicCompletionIntegers F ∧
        ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v ∈ v.adicCompletionIntegers F := by
  constructor
  · intro h
    refine ⟨h.le, ?_⟩
    have h1 := fin_mul_inv g v
    have h2 : Valued.v ((g : AdeleRing (𝓞 F) F).2 v) *
        Valued.v (((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v) = 1 := by
      rw [← map_mul, h1, map_one]
    rw [h, one_mul] at h2
    exact h2.le
  · intro h
    exact valued_eq_one_of_mem (fin_mul_inv g v) h.1 h.2

/-- The subgroup of ideles that are units outside `S`. -/
def sIntSubgroup (Sf : Finset (HeightOneSpectrum (𝓞 F))) : Subgroup (IdeleGroup F) where
  carrier := sIntegralIdeles Sf
  mul_mem' := by
    intro a b ha hb v hv
    change Valued.v ((a : AdeleRing (𝓞 F) F).2 v * (b : AdeleRing (𝓞 F) F).2 v) = 1
    rw [map_mul, ha v hv, hb v hv, one_mul]
  one_mem' := by
    intro v _
    change Valued.v (1 : v.adicCompletion F) = 1
    exact map_one _
  inv_mem' := by
    intro a ha v hv
    have h := (valued_eq_one_iff a v).mp (ha v hv)
    apply (valued_eq_one_iff a⁻¹ v).mpr
    rw [inv_inv]
    exact ⟨h.2, h.1⟩

theorem isOpen_sIntegralIdeles (Sf : Finset (HeightOneSpectrum (𝓞 F))) :
    IsOpen (sIntegralIdeles Sf : Set (IdeleGroup F)) := by
  have hs := isOpen_rp_forall_mem (G := fun v : HeightOneSpectrum (𝓞 F) ↦ v.adicCompletion F)
    (A := fun v ↦ (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    {v | v ∉ Sf} (fun v ↦ isOpen_adicCompletionIntegers v)
  have c1 : Continuous (fun g : IdeleGroup F ↦ ((g : AdeleRing (𝓞 F) F).2 :
      Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F])) :=
    continuous_snd.comp Units.continuous_val
  have c2 : Continuous (fun g : IdeleGroup F ↦ (((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 :
      Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F])) :=
    continuous_snd.comp Units.continuous_coe_inv
  convert (hs.preimage c1).inter (hs.preimage c2) using 1
  ext g
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · intro h
    exact ⟨fun v hv ↦ ((valued_eq_one_iff g v).mp (h v hv)).1,
      fun v hv ↦ ((valued_eq_one_iff g v).mp (h v hv)).2⟩
  · intro h v hv
    exact (valued_eq_one_iff g v).mpr ⟨h.1 v hv, h.2 v hv⟩

theorem ideleNorm_eq_of_mk_eq {a b : IdeleGroup F}
    (h : (QuotientGroup.mk a : IdeleClassGroup F) = QuotientGroup.mk b) :
    ideleNorm a = ideleNorm b := by
  obtain ⟨ξ, hξ⟩ := QuotientGroup.eq.mp h
  have : b = a * principalIdele F ξ := by rw [hξ, mul_inv_cancel_left]
  rw [this, ideleNorm_mul, ideleNorm_principal, mul_one]

theorem isCompact_sNormOne (Sf : Finset (HeightOneSpectrum (𝓞 F))) :
    IsCompact ((QuotientGroup.mk : IdeleGroup F → IdeleClassGroup F) ''
      (sIntegralIdeles Sf ∩ {g | ideleNorm g = 1})) := by
  let N := principalIdeles F
  let H := (sIntSubgroup Sf).map (QuotientGroup.mk' N)
  have hHset : (H : Set (IdeleClassGroup F)) =
      (QuotientGroup.mk : IdeleGroup F → IdeleClassGroup F) '' sIntegralIdeles Sf := by
    ext c
    simp only [H, Subgroup.coe_map, QuotientGroup.coe_mk']
    rfl
  have hHopen : IsOpen (H : Set (IdeleClassGroup F)) := by
    rw [hHset]
    exact QuotientGroup.isOpenMap_coe _ (isOpen_sIntegralIdeles Sf)
  have hHclosed : IsClosed (H : Set (IdeleClassGroup F)) := Subgroup.isClosed_of_isOpen H hHopen
  have heq : (QuotientGroup.mk : IdeleGroup F → IdeleClassGroup F) ''
      (sIntegralIdeles Sf ∩ {g | ideleNorm g = 1}) =
      (H : Set (IdeleClassGroup F)) ∩
        (QuotientGroup.mk : IdeleGroup F → IdeleClassGroup F) '' {g | ideleNorm g = 1} := by
    rw [hHset]
    apply Set.Subset.antisymm
    · rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
      exact ⟨⟨g, hg1, rfl⟩, ⟨g, hg2, rfl⟩⟩
    · rintro c ⟨⟨s, hs, rfl⟩, ⟨j, hj, hjs⟩⟩
      refine ⟨s, ⟨hs, ?_⟩, rfl⟩
      change ideleNorm s = 1
      rw [← ideleNorm_eq_of_mk_eq hjs]
      exact hj
  rw [heq]
  exact (isCompact_normOne (F := F)).inter_left hHclosed

end SCompact

section Count1

variable {F : Type*} [Field F] [NumberField F]

theorem inf_norm_coe (w : InfinitePlace F) (x : F) : ‖(x : w.Completion)‖ = w x := by
  have h := InfinitePlace.Completion.norm_coe w ((WithAbs.equiv w.1).symm x)
  rw [WithAbs.equiv_symm_apply] at h
  exact h

theorem toNNReal_exp_eq (v : HeightOneSpectrum (𝓞 F))
    (he : (Ideal.absNorm v.asIdeal : NNReal) ≠ 0) (K : ℤ) :
    (WithZeroMulInt.toNNReal he (WithZero.exp K) : ℝ) = (Ideal.absNorm v.asIdeal : ℝ) ^ K := by
  rw [WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero, WithZero.toAdd_unzero_eq_log,
    WithZero.log_exp]
  push_cast
  rfl

theorem valuation_le_exp_of_norm_le (v : HeightOneSpectrum (𝓞 F)) (x : F) (K : ℕ) (R : ℝ)
    (hK : Real.exp R < 2 ^ K) (hx : ‖(x : v.adicCompletion F)‖ ≤ Real.exp R) :
    v.valuation F x ≤ WithZero.exp (K : ℤ) := by
  by_contra h
  push Not at h
  have he : (1 : NNReal) < (Ideal.absNorm v.asIdeal : NNReal) :=
    NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v
  have hm := WithZeroMulInt.toNNReal_strictMono he h
  have h1 : ((WithZeroMulInt.toNNReal he.ne_zero (WithZero.exp (K : ℤ)) : NNReal) : ℝ) <
      ((WithZeroMulInt.toNNReal he.ne_zero (v.valuation F x) : NNReal) : ℝ) := by
    exact_mod_cast hm
  rw [toNNReal_exp_eq] at h1
  have hn : ‖(x : v.adicCompletion F)‖ =
      ((WithZeroMulInt.toNNReal he.ne_zero (v.valuation F x) : NNReal) : ℝ) := by
    rw [FinitePlace.norm_def, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  have h2 : (2 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := by
    have := NumberField.HeightOneSpectrum.one_lt_absNorm v
    exact_mod_cast this
  have h3 : (2 : ℝ) ^ K ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ K :=
    pow_le_pow_left₀ (by norm_num) h2 K
  have h4 : (Ideal.absNorm v.asIdeal : ℝ) ^ (K : ℤ) = (Ideal.absNorm v.asIdeal : ℝ) ^ K :=
    zpow_natCast _ K
  rw [h4] at h1
  linarith

open Classical in
theorem valuation_prodPi (Sf : Finset (HeightOneSpectrum (𝓞 F))) (K : ℕ)
    (π : HeightOneSpectrum (𝓞 F) → Fˣ)
    (hπ : ∀ v w : HeightOneSpectrum (𝓞 F), w.valuation F (π v : F) =
      if w = v then WithZero.exp (-(classNumber F : ℤ)) else 1)
    (w : HeightOneSpectrum (𝓞 F)) :
    w.valuation F ((∏ v ∈ Sf, π v ^ K : Fˣ) : F) =
      if w ∈ Sf then WithZero.exp (-(classNumber F : ℤ)) ^ K else 1 := by
  classical
  have : ((∏ v ∈ Sf, π v ^ K : Fˣ) : F) = ∏ v ∈ Sf, (π v : F) ^ K := by
    simp only [Units.coe_prod, Units.val_pow_eq_pow_val]
  rw [this, map_prod]
  simp only [map_pow, hπ]
  have e : ∀ v ∈ Sf, (if w = v then WithZero.exp (-(classNumber F : ℤ)) else 1) ^ K =
      if w = v then WithZero.exp (-(classNumber F : ℤ)) ^ K else 1 := by
    intro v _
    split_ifs <;> simp
  rw [Finset.prod_congr rfl e, Finset.prod_ite_eq]

theorem finite_B (Sf : Finset (HeightOneSpectrum (𝓞 F))) (R : ℝ) :
    {ζ : Fˣ | ζ ∈ SUnits Sf ∧ (∀ w : InfinitePlace F, w (ζ : F) ≤ Real.exp R) ∧
      ∀ v : Sf, ‖((ζ : F) : (v : HeightOneSpectrum (𝓞 F)).adicCompletion F)‖ ≤ Real.exp R}.Finite := by
  classical
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt (Real.exp R) (by norm_num : (1 : ℝ) < 2)
  let π : HeightOneSpectrum (𝓞 F) → Fˣ := fun v ↦ (exists_prime_power_generator v).choose
  have hπ : ∀ v w : HeightOneSpectrum (𝓞 F), w.valuation F (π v : F) =
      if w = v then WithZero.exp (-(classNumber F : ℤ)) else 1 :=
    fun v ↦ (exists_prime_power_generator v).choose_spec
  let D : Fˣ := ∏ v ∈ Sf, π v ^ K
  have hD := valuation_prodPi Sf K π hπ
  let B : ℝ := Real.exp R * ∑ φ : F →+* ℂ, ‖φ (D : F)‖
  apply Set.Finite.of_finite_image (f := fun ζ : Fˣ ↦ (ζ : F) * (D : F))
  · apply (NumberField.Embeddings.finite_of_norm_le F ℂ B).subset
    rintro _ ⟨ζ, ⟨hS, hinf, hfin⟩, rfl⟩
    constructor
    · have hle : ∀ w : HeightOneSpectrum (𝓞 F), w.valuation F ((ζ : F) * D) ≤ 1 := by
        intro w
        rw [map_mul, hD w]
        by_cases hw : w ∈ Sf
        · rw [if_pos hw]
          have h1 := valuation_le_exp_of_norm_le w (ζ : F) K R hK (hfin ⟨w, hw⟩)
          have hh : (1 : ℤ) ≤ (classNumber F : ℤ) := by
            have := NumberField.classNumber_ne_zero F
            omega
          calc w.valuation F (ζ : F) * WithZero.exp (-(classNumber F : ℤ)) ^ K
              ≤ WithZero.exp (K : ℤ) * WithZero.exp (-(classNumber F : ℤ)) ^ K :=
                mul_le_mul' h1 le_rfl
            _ = WithZero.exp ((K : ℤ) + K • (-(classNumber F : ℤ))) := by
                rw [WithZero.exp_add, WithZero.exp_nsmul]
            _ ≤ 1 := by
                rw [← WithZero.exp_zero, WithZero.exp_le_exp, nsmul_eq_mul]
                have h2 : (0 : ℤ) ≤ (K : ℤ) := Int.natCast_nonneg _
                nlinarith
        · rw [if_neg hw, mul_one]
          exact (hS w hw).le
      obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F _ hle
      show IsIntegral ℤ ((ζ : F) * D)
      rw [← hr]
      exact NumberField.RingOfIntegers.isIntegral_coe r
    · intro φ
      rw [map_mul, norm_mul]
      have h1 : ‖φ (ζ : F)‖ ≤ Real.exp R := by
        rw [← InfinitePlace.apply]
        exact hinf _
      have h2 : ‖φ (D : F)‖ ≤ ∑ ψ : F →+* ℂ, ‖ψ (D : F)‖ :=
        Finset.single_le_sum (f := fun ψ : F →+* ℂ ↦ ‖ψ (D : F)‖) (fun _ _ ↦ norm_nonneg _)
          (Finset.mem_univ φ)
      exact mul_le_mul h1 h2 (norm_nonneg _) (Real.exp_pos R).le
  · intro a _ b _ h
    exact Units.ext (mul_right_cancel₀ D.ne_zero h)

end Count1

section Count2

variable {F : Type*} [Field F] [NumberField F]

theorem fin_coe_ne_zero (v : HeightOneSpectrum (𝓞 F)) {x : F} (hx : x ≠ 0) :
    ((x : F) : v.adicCompletion F) ≠ 0 := by
  show FinitePlace.embedding v x ≠ 0
  exact (map_ne_zero _).mpr hx

theorem fin_coe_mul (v : HeightOneSpectrum (𝓞 F)) (x y : F) :
    ((x * y : F) : v.adicCompletion F) = (x : v.adicCompletion F) * (y : v.adicCompletion F) :=
  map_mul (FinitePlace.embedding v) x y

theorem fin_coe_one (v : HeightOneSpectrum (𝓞 F)) :
    ((1 : F) : v.adicCompletion F) = 1 :=
  map_one (FinitePlace.embedding v)

/-- Local logarithms of an element of `Fˣ` at the places of `S`. -/
noncomputable def lam (Sf : Finset (HeightOneSpectrum (𝓞 F))) (ξ : Fˣ) :
    InfinitePlace F ⊕ Sf → ℝ :=
  Sum.elim (fun w ↦ (w.mult : ℝ) * Real.log (w (ξ : F)))
    (fun v ↦ Real.log ‖((ξ : F) : (v : HeightOneSpectrum (𝓞 F)).adicCompletion F)‖)

theorem lam_mul (Sf : Finset (HeightOneSpectrum (𝓞 F))) (ξ η : Fˣ) :
    lam Sf (ξ * η) = lam Sf ξ + lam Sf η := by
  funext i
  rcases i with w | v
  · simp only [lam, Sum.elim_inl, Pi.add_apply, Units.val_mul, map_mul]
    rw [Real.log_mul (InfinitePlace.pos_iff.mpr ξ.ne_zero).ne'
      (InfinitePlace.pos_iff.mpr η.ne_zero).ne']
    ring
  · simp only [lam, Sum.elim_inr, Pi.add_apply, Units.val_mul]
    rw [fin_coe_mul, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr (fin_coe_ne_zero _ ξ.ne_zero))
      (norm_ne_zero_iff.mpr (fin_coe_ne_zero _ η.ne_zero))]

theorem lam_one (Sf : Finset (HeightOneSpectrum (𝓞 F))) : lam Sf 1 = 0 := by
  funext i
  rcases i with w | v
  · simp only [lam, Sum.elim_inl, Units.val_one, map_one, Real.log_one, mul_zero, Pi.zero_apply]
  · simp only [lam, Sum.elim_inr, Units.val_one, Pi.zero_apply]
    rw [fin_coe_one, norm_one, Real.log_one]

theorem lam_inv (Sf : Finset (HeightOneSpectrum (𝓞 F))) (ξ : Fˣ) :
    lam Sf ξ⁻¹ = -lam Sf ξ := by
  have h := lam_mul Sf ξ⁻¹ ξ
  rw [inv_mul_cancel, lam_one] at h
  funext i
  have hi := congrFun h i
  simp only [Pi.zero_apply, Pi.add_apply] at hi
  simp only [Pi.neg_apply]
  linarith

theorem sProduct (Sf : Finset (HeightOneSpectrum (𝓞 F))) (ξ : Fˣ) (hξ : ξ ∈ SUnits Sf) :
    (∏ w : InfinitePlace F, w (ξ : F) ^ w.mult) *
      ∏ v : Sf, ‖((ξ : F) : (v : HeightOneSpectrum (𝓞 F)).adicCompletion F)‖ = 1 := by
  have pf := product_formula (ξ : F) ξ.ne_zero
  simp only [inf_norm_coe] at pf
  have hfin : (∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖((ξ : F) : v.adicCompletion F)‖) =
      ∏ v ∈ Sf, ‖((ξ : F) : v.adicCompletion F)‖ := by
    apply finprod_eq_prod_of_mulSupport_subset
    intro v hv
    by_contra h
    apply hv
    apply norm_eq_one_of_valued
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact hξ v h
  rw [hfin, ← Finset.prod_coe_sort Sf] at pf
  exact pf

theorem sum_lam (Sf : Finset (HeightOneSpectrum (𝓞 F))) (ξ : Fˣ) (hξ : ξ ∈ SUnits Sf) :
    ∑ i, lam Sf ξ i = 0 := by
  rw [Fintype.sum_sum_type]
  simp only [lam, Sum.elim_inl, Sum.elim_inr]
  have h0 : ∀ w : InfinitePlace F, w (ξ : F) ^ w.mult ≠ 0 :=
    fun w ↦ pow_ne_zero _ (InfinitePlace.pos_iff.mpr ξ.ne_zero).ne'
  have h1 : ∀ v : Sf, ‖((ξ : F) : (v : HeightOneSpectrum (𝓞 F)).adicCompletion F)‖ ≠ 0 :=
    fun v ↦ norm_ne_zero_iff.mpr (fin_coe_ne_zero _ ξ.ne_zero)
  have e1 : ∑ w : InfinitePlace F, (w.mult : ℝ) * Real.log (w (ξ : F)) =
      Real.log (∏ w : InfinitePlace F, w (ξ : F) ^ w.mult) := by
    rw [Real.log_prod (fun w _ ↦ h0 w)]
    apply Finset.sum_congr rfl
    intro w _
    rw [Real.log_pow]
  have e2 : ∑ v : Sf, Real.log ‖((ξ : F) : (v : HeightOneSpectrum (𝓞 F)).adicCompletion F)‖ =
      Real.log (∏ v : Sf, ‖((ξ : F) : (v : HeightOneSpectrum (𝓞 F)).adicCompletion F)‖) :=
    (Real.log_prod (fun v _ ↦ h1 v)).symm
  rw [e1, e2, ← Real.log_mul (Finset.prod_ne_zero_iff.mpr fun w _ ↦ h0 w)
    (Finset.prod_ne_zero_iff.mpr fun v _ ↦ h1 v), sProduct Sf ξ hξ, Real.log_one]

theorem sg_inf_ne (Sf : Finset (HeightOneSpectrum (𝓞 F))) (g : SIdeleGroup F Sf)
    (w : InfinitePlace F) : (g : SAdeleRing F Sf).1 w ≠ 0 := by
  intro h
  have h1 := congrArg (fun a : SAdeleRing F Sf ↦ a.1 w) g.mul_inv
  change (g : SAdeleRing F Sf).1 w * ((g⁻¹ : SIdeleGroup F Sf) : SAdeleRing F Sf).1 w = 1 at h1
  rw [h, zero_mul] at h1
  exact zero_ne_one h1

theorem sg_fin_ne (Sf : Finset (HeightOneSpectrum (𝓞 F))) (g : SIdeleGroup F Sf)
    (v : Sf) : (g : SAdeleRing F Sf).2 v ≠ 0 := by
  intro h
  have h1 := congrArg (fun a : SAdeleRing F Sf ↦ a.2 v) g.mul_inv
  change (g : SAdeleRing F Sf).2 v * ((g⁻¹ : SIdeleGroup F Sf) : SAdeleRing F Sf).2 v = 1 at h1
  rw [h, zero_mul] at h1
  exact zero_ne_one h1

/-- Local logarithms of an `S`-idele. -/
noncomputable def gam (Sf : Finset (HeightOneSpectrum (𝓞 F))) (g : SIdeleGroup F Sf) :
    InfinitePlace F ⊕ Sf → ℝ :=
  Sum.elim (fun w ↦ (w.mult : ℝ) * Real.log ‖(g : SAdeleRing F Sf).1 w‖)
    (fun v ↦ Real.log ‖(g : SAdeleRing F Sf).2 v‖)

theorem sIdeleNorm_pos (Sf : Finset (HeightOneSpectrum (𝓞 F))) (g : SIdeleGroup F Sf) :
    0 < sIdeleNorm Sf g := by
  unfold sIdeleNorm
  apply mul_pos
  · exact Finset.prod_pos fun w _ ↦ pow_pos (norm_pos_iff.mpr (sg_inf_ne Sf g w)) _
  · exact Finset.prod_pos fun v _ ↦ norm_pos_iff.mpr (sg_fin_ne Sf g v)

theorem sum_gam (Sf : Finset (HeightOneSpectrum (𝓞 F))) (g : SIdeleGroup F Sf) :
    ∑ i, gam Sf g i = Real.log (sIdeleNorm Sf g) := by
  rw [Fintype.sum_sum_type]
  simp only [gam, Sum.elim_inl, Sum.elim_inr]
  have h0 : ∀ w : InfinitePlace F, ‖(g : SAdeleRing F Sf).1 w‖ ^ w.mult ≠ 0 :=
    fun w ↦ pow_ne_zero _ (norm_ne_zero_iff.mpr (sg_inf_ne Sf g w))
  have h1 : ∀ v : Sf, ‖(g : SAdeleRing F Sf).2 v‖ ≠ 0 :=
    fun v ↦ norm_ne_zero_iff.mpr (sg_fin_ne Sf g v)
  have e1 : ∑ w : InfinitePlace F, (w.mult : ℝ) * Real.log ‖(g : SAdeleRing F Sf).1 w‖ =
      Real.log (∏ w : InfinitePlace F, ‖(g : SAdeleRing F Sf).1 w‖ ^ w.mult) := by
    rw [Real.log_prod (fun w _ ↦ h0 w)]
    apply Finset.sum_congr rfl
    intro w _
    rw [Real.log_pow]
  have e2 : ∑ v : Sf, Real.log ‖(g : SAdeleRing F Sf).2 v‖ =
      Real.log (∏ v : Sf, ‖(g : SAdeleRing F Sf).2 v‖) :=
    (Real.log_prod (fun v _ ↦ h1 v)).symm
  rw [e1, e2, ← Real.log_mul (Finset.prod_ne_zero_iff.mpr fun w _ ↦ h0 w)
    (Finset.prod_ne_zero_iff.mpr fun v _ ↦ h1 v)]
  rfl

theorem box_le (Sf : Finset (HeightOneSpectrum (𝓞 F))) (g : SIdeleGroup F Sf) (ξ : Fˣ)
    (hinf : ∀ w : InfinitePlace F,
      ‖(sDiagonal Sf (ξ : F) * (g : SAdeleRing F Sf)).1 w‖ ≤ 1)
    (hfin : ∀ v : Sf, (sDiagonal Sf (ξ : F) * (g : SAdeleRing F Sf)).2 v ∈
      (v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F) :
    ∀ i, lam Sf ξ i + gam Sf g i ≤ 0 := by
  intro i
  rcases i with w | v
  · simp only [lam, gam, Sum.elim_inl]
    have h1 : ‖(sDiagonal Sf (ξ : F) * (g : SAdeleRing F Sf)).1 w‖ =
        w (ξ : F) * ‖(g : SAdeleRing F Sf).1 w‖ := by
      change ‖((ξ : F) : w.Completion) * (g : SAdeleRing F Sf).1 w‖ = _
      rw [norm_mul, inf_norm_coe]
    have h2 := hinf w
    rw [h1] at h2
    have hp1 : 0 < w (ξ : F) := InfinitePlace.pos_iff.mpr ξ.ne_zero
    have hp2 : 0 < ‖(g : SAdeleRing F Sf).1 w‖ := norm_pos_iff.mpr (sg_inf_ne Sf g w)
    have h3 : Real.log (w (ξ : F)) + Real.log ‖(g : SAdeleRing F Sf).1 w‖ ≤ 0 := by
      rw [← Real.log_mul hp1.ne' hp2.ne']
      exact Real.log_nonpos (mul_pos hp1 hp2).le h2
    have hm : (0 : ℝ) ≤ (w.mult : ℝ) := Nat.cast_nonneg _
    nlinarith
  · simp only [lam, gam, Sum.elim_inr]
    have h1 : ‖(sDiagonal Sf (ξ : F) * (g : SAdeleRing F Sf)).2 v‖ =
        ‖((ξ : F) : (v : HeightOneSpectrum (𝓞 F)).adicCompletion F)‖ *
          ‖(g : SAdeleRing F Sf).2 v‖ := by
      change ‖((ξ : F) : (v : HeightOneSpectrum (𝓞 F)).adicCompletion F) *
        (g : SAdeleRing F Sf).2 v‖ = _
      rw [norm_mul]
    have h2 : ‖(sDiagonal Sf (ξ : F) * (g : SAdeleRing F Sf)).2 v‖ ≤ 1 :=
      Valued.toNormedField.norm_le_one_iff.mpr (hfin v)
    rw [h1] at h2
    have hp1 : 0 < ‖((ξ : F) : (v : HeightOneSpectrum (𝓞 F)).adicCompletion F)‖ :=
      norm_pos_iff.mpr (fin_coe_ne_zero _ ξ.ne_zero)
    have hp2 : 0 < ‖(g : SAdeleRing F Sf).2 v‖ := norm_pos_iff.mpr (sg_fin_ne Sf g v)
    rw [← Real.log_mul hp1.ne' hp2.ne']
    exact Real.log_nonpos (mul_pos hp1 hp2).le h2

end Count2

section Count3

variable {F : Type*} [Field F] [NumberField F]

theorem mem_B_of_lam (Sf : Finset (HeightOneSpectrum (𝓞 F))) (R : ℝ) (hR : 0 ≤ R) (ζ : Fˣ)
    (hS : ζ ∈ SUnits Sf) (h : ∀ i, lam Sf ζ i ≤ R) :
    ζ ∈ {ζ : Fˣ | ζ ∈ SUnits Sf ∧ (∀ w : InfinitePlace F, w (ζ : F) ≤ Real.exp R) ∧
      ∀ v : Sf, ‖((ζ : F) : (v : HeightOneSpectrum (𝓞 F)).adicCompletion F)‖ ≤ Real.exp R} := by
  refine ⟨hS, fun w ↦ ?_, fun v ↦ ?_⟩
  · have h1 := h (Sum.inl w)
    simp only [lam, Sum.elim_inl] at h1
    have hp : 0 < w (ζ : F) := InfinitePlace.pos_iff.mpr ζ.ne_zero
    apply (Real.log_le_iff_le_exp hp).mp
    have hm : (1 : ℝ) ≤ (w.mult : ℝ) := by exact_mod_cast InfinitePlace.one_le_mult
    by_cases hl : Real.log (w (ζ : F)) ≤ 0
    · linarith
    · push Not at hl
      nlinarith
  · have h1 := h (Sum.inr v)
    simp only [lam, Sum.elim_inr] at h1
    have hp : 0 < ‖((ζ : F) : (v : HeightOneSpectrum (𝓞 F)).adicCompletion F)‖ :=
      norm_pos_iff.mpr (fin_coe_ne_zero _ ζ.ne_zero)
    exact (Real.log_le_iff_le_exp hp).mp h1

theorem count_bound (Sf : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ C ε : ℝ, 0 < C ∧ 0 < ε ∧ ∀ g : SIdeleGroup F Sf, sIdeleNorm Sf g < ε →
      {ξ : Fˣ | ξ ∈ SUnits Sf ∧
        (∀ w : InfinitePlace F, ‖(sDiagonal Sf (ξ : F) * (g : SAdeleRing F Sf)).1 w‖ ≤ 1) ∧
        ∀ v : Sf, (sDiagonal Sf (ξ : F) * (g : SAdeleRing F Sf)).2 v ∈
          (v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F}.Finite ∧
      (({ξ : Fˣ | ξ ∈ SUnits Sf ∧
        (∀ w : InfinitePlace F, ‖(sDiagonal Sf (ξ : F) * (g : SAdeleRing F Sf)).1 w‖ ≤ 1) ∧
        ∀ v : Sf, (sDiagonal Sf (ξ : F) * (g : SAdeleRing F Sf)).2 v ∈
          (v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F}.ncard : ℝ) ≤
        C * |Real.log (sIdeleNorm Sf g)| ^
          (InfinitePlace.nrRealPlaces F + InfinitePlace.nrComplexPlaces F + Sf.card - 1)) := by
  classical
  obtain ⟨w0⟩ : Nonempty (InfinitePlace F) := inferInstance
  let i0 : InfinitePlace F ⊕ Sf := Sum.inl w0
  let J := {i : InfinitePlace F ⊕ Sf // i ≠ i0}
  let n := InfinitePlace.nrRealPlaces F + InfinitePlace.nrComplexPlaces F + Sf.card - 1
  have hcardJ : Fintype.card J = n := by
    have h1 : Fintype.card J = Fintype.card (InfinitePlace F ⊕ Sf) - 1 := by
      have := Fintype.card_subtype_compl (fun i : InfinitePlace F ⊕ Sf ↦ i = i0)
      rw [Fintype.card_subtype_eq] at this
      exact this
    rw [h1, Fintype.card_sum, Fintype.card_coe,
      InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
  let R : ℝ := (Fintype.card J : ℝ) + 1
  have hR0 : (0 : ℝ) ≤ R := by positivity
  let Bs := {ζ : Fˣ | ζ ∈ SUnits Sf ∧ (∀ w : InfinitePlace F, w (ζ : F) ≤ Real.exp R) ∧
      ∀ v : Sf, ‖((ζ : F) : (v : HeightOneSpectrum (𝓞 F)).adicCompletion F)‖ ≤ Real.exp R}
  have hB : Bs.Finite := finite_B Sf R
  let nB := hB.toFinset.card
  refine ⟨((nB : ℝ) + 1) * 4 ^ n, Real.exp (-1), by positivity, Real.exp_pos _, fun g hg ↦ ?_⟩
  let X := {ξ : Fˣ | ξ ∈ SUnits Sf ∧
        (∀ w : InfinitePlace F, ‖(sDiagonal Sf (ξ : F) * (g : SAdeleRing F Sf)).1 w‖ ≤ 1) ∧
        ∀ v : Sf, (sDiagonal Sf (ξ : F) * (g : SAdeleRing F Sf)).2 v ∈
          (v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F}
  change X.Finite ∧ (X.ncard : ℝ) ≤ ((nB : ℝ) + 1) * 4 ^ n *
    |Real.log (sIdeleNorm Sf g)| ^ n
  have hpos := sIdeleNorm_pos Sf g
  let L : ℝ := -Real.log (sIdeleNorm Sf g)
  have hL1 : 1 < L := by
    have := Real.log_lt_log hpos hg
    rw [Real.log_exp] at this
    show 1 < -Real.log (sIdeleNorm Sf g)
    linarith
  have habs : |Real.log (sIdeleNorm Sf g)| = L := by
    rw [abs_of_neg (by linarith)]
  let y : Fˣ → InfinitePlace F ⊕ Sf → ℝ := fun ξ ↦ lam Sf ξ + gam Sf g
  have hy : ∀ ξ ∈ X, ∀ i, y ξ i ≤ 0 := fun ξ hξ ↦ box_le Sf g ξ hξ.2.1 hξ.2.2
  have hsum : ∀ ξ ∈ X, ∑ i, y ξ i = -L := by
    intro ξ hξ
    simp only [y, Pi.add_apply, Finset.sum_add_distrib, sum_lam Sf ξ hξ.1, sum_gam, zero_add, L,
      neg_neg]
  have hlow : ∀ ξ ∈ X, ∀ i, -L ≤ y ξ i := by
    intro ξ hξ i
    have h1 : -y ξ i ≤ ∑ j, -y ξ j :=
      Finset.single_le_sum (f := fun j ↦ -y ξ j) (fun j _ ↦ by linarith [hy ξ hξ j])
        (Finset.mem_univ i)
    rw [Finset.sum_neg_distrib, hsum ξ hξ] at h1
    linarith
  let M : ℕ := ⌈L⌉₊ + 1
  let T : Finset (J → ℤ) := Fintype.piFinset (fun _ ↦ Finset.Icc (-(M : ℤ)) 0)
  let kmap : Fˣ → J → ℤ := fun ξ j ↦ ⌊y ξ j.1⌋
  have hk : ∀ ξ ∈ X, kmap ξ ∈ T := by
    intro ξ hξ
    rw [Fintype.mem_piFinset]
    intro j
    rw [Finset.mem_Icc]
    constructor
    · apply Int.le_floor.mpr
      have h1 := hlow ξ hξ j.1
      have h2 : L ≤ (⌈L⌉₊ : ℝ) := Nat.le_ceil L
      push_cast [M]
      linarith
    · exact Int.floor_nonpos (hy ξ hξ j.1)
  have hfib : ∀ ξ ∈ X, ∀ η ∈ X, kmap ξ = kmap η → ξ * η⁻¹ ∈ Bs := by
    intro ξ hξ η hη hkk
    have hS : ξ * η⁻¹ ∈ SUnits Sf := (SUnits Sf).mul_mem hξ.1 ((SUnits Sf).inv_mem hη.1)
    have hl : ∀ i, lam Sf (ξ * η⁻¹) i = y ξ i - y η i := by
      intro i
      rw [lam_mul, lam_inv]
      simp only [y, Pi.add_apply, Pi.neg_apply]
      ring
    have hJ : ∀ j : J, lam Sf (ξ * η⁻¹) j.1 < 1 ∧ -lam Sf (ξ * η⁻¹) j.1 < 1 := by
      intro j
      have := Int.abs_sub_lt_one_of_floor_eq_floor (congrFun hkk j)
      rw [hl]
      constructor
      · linarith [le_abs_self (y ξ j.1 - y η j.1)]
      · linarith [neg_abs_le (y ξ j.1 - y η j.1)]
    apply mem_B_of_lam Sf R hR0 _ hS
    intro i
    by_cases hi : i = i0
    · have hz := sum_lam Sf (ξ * η⁻¹) hS
      rw [Fintype.sum_eq_add_sum_subtype_ne _ i0] at hz
      have hbound : ∑ j : J, -lam Sf (ξ * η⁻¹) j.1 ≤ ∑ _j : J, (1 : ℝ) :=
        Finset.sum_le_sum fun j _ ↦ (hJ j).2.le
      rw [Finset.sum_neg_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        mul_one] at hbound
      rw [hi]
      change lam Sf (ξ * η⁻¹) i0 ≤ (Fintype.card J : ℝ) + 1
      have : lam Sf (ξ * η⁻¹) i0 = -∑ j : J, lam Sf (ξ * η⁻¹) j.1 := by linarith
      linarith
    · have := (hJ ⟨i, hi⟩).1
      have hJ0 : (0 : ℝ) ≤ (Fintype.card J : ℝ) := Nat.cast_nonneg _
      change lam Sf (ξ * η⁻¹) i ≤ (Fintype.card J : ℝ) + 1
      linarith
  have hpiece : ∀ t : J → ℤ, {ξ | ξ ∈ X ∧ kmap ξ = t}.Finite := by
    intro t
    by_cases hne : {ξ | ξ ∈ X ∧ kmap ξ = t}.Nonempty
    · obtain ⟨ξ0, hξ0, hξ0t⟩ := hne
      apply (hB.image (fun ζ ↦ ζ * ξ0)).subset
      rintro ξ ⟨hξ, hξt⟩
      refine ⟨ξ * ξ0⁻¹, hfib ξ hξ ξ0 hξ0 (hξt.trans hξ0t.symm), ?_⟩
      simp only [inv_mul_cancel_right]
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      rw [hne]
      exact Set.finite_empty
  have hXfin : X.Finite := by
    apply (Set.Finite.biUnion T.finite_toSet (fun t _ ↦ hpiece t)).subset
    intro ξ hξ
    exact Set.mem_biUnion (x := kmap ξ) (hk ξ hξ) ⟨hξ, rfl⟩
  refine ⟨hXfin, ?_⟩
  have hcard : X.ncard ≤ nB * T.card := by
    rw [Set.ncard_eq_toFinset_card X hXfin]
    apply Finset.card_le_mul_card_image_of_maps_to (f := kmap)
    · intro a ha
      exact hk a ((Set.Finite.mem_toFinset hXfin).mp ha)
    · intro b _
      by_cases hne : (hXfin.toFinset.filter (fun a ↦ kmap a = b)).Nonempty
      · obtain ⟨a0, ha0⟩ := hne
        rw [Finset.mem_filter, Set.Finite.mem_toFinset] at ha0
        calc (hXfin.toFinset.filter (fun a ↦ kmap a = b)).card
            ≤ (hB.toFinset.image (fun ζ ↦ ζ * a0)).card := by
              apply Finset.card_le_card
              intro a ha
              rw [Finset.mem_filter, Set.Finite.mem_toFinset] at ha
              rw [Finset.mem_image]
              refine ⟨a * a0⁻¹, ?_, by simp only [inv_mul_cancel_right]⟩
              rw [Set.Finite.mem_toFinset]
              exact hfib a ha.1 a0 ha0.1 (ha.2.trans ha0.2.symm)
          _ ≤ nB := Finset.card_image_le
      · rw [Finset.not_nonempty_iff_eq_empty] at hne
        rw [hne, Finset.card_empty]
        exact Nat.zero_le _
  have hT : T.card = (M + 1) ^ Fintype.card J := by
    simp only [T, Fintype.card_piFinset, Int.card_Icc, Finset.prod_const, Finset.card_univ]
    congr 1
    omega
  rw [hT, hcardJ] at hcard
  have hcardR : (X.ncard : ℝ) ≤ (nB : ℝ) * ((M : ℝ) + 1) ^ n := by
    exact_mod_cast hcard
  have hM : ((M : ℝ) + 1) ≤ 4 * L := by
    have h1 : (⌈L⌉₊ : ℝ) < L + 1 := Nat.ceil_lt_add_one (by linarith)
    push_cast [M]
    linarith
  have hM0 : (0 : ℝ) ≤ (M : ℝ) + 1 := by positivity
  have hpow : ((M : ℝ) + 1) ^ n ≤ (4 * L) ^ n := pow_le_pow_left₀ hM0 hM n
  rw [habs, mul_pow] at *
  have hL0 : (0 : ℝ) ≤ L ^ n := pow_nonneg (by linarith) n
  have h4 : (0 : ℝ) ≤ 4 ^ n := by positivity
  have hnB : (0 : ℝ) ≤ (nB : ℝ) := Nat.cast_nonneg _
  calc (X.ncard : ℝ) ≤ (nB : ℝ) * ((M : ℝ) + 1) ^ n := hcardR
    _ ≤ (nB : ℝ) * (4 ^ n * L ^ n) := mul_le_mul_of_nonneg_left hpow hnB
    _ ≤ ((nB : ℝ) + 1) * (4 ^ n * L ^ n) :=
        mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg h4 hL0)
    _ = ((nB : ℝ) + 1) * 4 ^ n * L ^ n := by ring

end Count3
end Aux_MasulloGRH_s_unit_lattice_point_count

namespace Aux_MasulloGRH_sLocalTheta_asymptotic_at_zero

open Filter Topology Aux_MasulloGRH_s_unit_lattice_point_count

section Struct
variable {F : Type*} [Field F] [NumberField F] {Sf : Finset (HeightOneSpectrum (𝓞 F))}

/-- sum norm on the infinite adeles -/
noncomputable def infN (y : InfiniteAdeleRing F) : ℝ := ∑ w : InfinitePlace F, ‖y w‖

lemma infN_nonneg (y : InfiniteAdeleRing F) : 0 ≤ infN y :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

lemma infN_add (y z : InfiniteAdeleRing F) : infN (y + z) ≤ infN y + infN z := by
  unfold infN
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun w _ => norm_add_le (y w) (z w)

lemma infN_zero : infN (0 : InfiniteAdeleRing F) = 0 := by
  unfold infN
  exact Finset.sum_eq_zero fun w _ => norm_zero

lemma infN_zsmul (z : ℤ) (y : InfiniteAdeleRing F) : infN (z • y) ≤ |(z : ℝ)| * infN y := by
  unfold infN
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun w _ => ?_
  have h := norm_zsmul_le z (y w)
  rw [Int.norm_eq_abs] at h
  exact h

lemma infN_sum {ι : Type*} (t : Finset ι) (f : ι → InfiniteAdeleRing F) :
    infN (∑ i ∈ t, f i) ≤ ∑ i ∈ t, infN (f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, infN_zero]
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (infN_add _ _).trans (add_le_add le_rfl ih)

lemma infN_continuous : Continuous (infN : InfiniteAdeleRing F → ℝ) :=
  continuous_finsetSum _ fun w _ => (continuous_apply w).norm

lemma norm_le_infN (y : InfiniteAdeleRing F) (w : InfinitePlace F) : ‖y w‖ ≤ infN y :=
  Finset.single_le_sum (f := fun w => ‖y w‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ w)

lemma fin_bdd {Γ : Subgroup (Multiplicative (SAdeleRing F Sf))}
    (hΓ : IsCompactlyGeneratedSubgroup Γ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x ∈ Γ, ∀ v : Sf, ‖(Multiplicative.toAdd x).2 v‖ ≤ R := by
  obtain ⟨U, hUc, -, -, hcl⟩ := hΓ
  have hc : Continuous (fun x : Multiplicative (SAdeleRing F Sf) =>
      ∑ v : Sf, ‖(Multiplicative.toAdd x).2 v‖) :=
    continuous_finsetSum _ fun v _ =>
      ((continuous_apply v).comp (continuous_snd.comp continuous_toAdd)).norm
  obtain ⟨C, hC⟩ := hUc.exists_bound_of_continuousOn hc.continuousOn
  let R := max C 0
  let B : Subgroup (Multiplicative (SAdeleRing F Sf)) :=
    { carrier := {x | ∀ v : Sf, ‖(Multiplicative.toAdd x).2 v‖ ≤ R}
      mul_mem' := fun {x y} hx hy => by
        intro v
        have h1 : ‖(Multiplicative.toAdd x).2 v‖ ≤ R := hx v
        have h2 : ‖(Multiplicative.toAdd y).2 v‖ ≤ R := hy v
        show ‖(Multiplicative.toAdd x + Multiplicative.toAdd y).2 v‖ ≤ R
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)
      one_mem' := by
        intro v
        show ‖(0 : SAdeleRing F Sf).2 v‖ ≤ R
        rw [Prod.snd_zero, Pi.zero_apply, norm_zero]
        exact le_max_right _ _
      inv_mem' := fun {x} hx => by
        intro v
        have h1 : ‖(Multiplicative.toAdd x).2 v‖ ≤ R := hx v
        show ‖(-Multiplicative.toAdd x).2 v‖ ≤ R
        rw [Prod.snd_neg, Pi.neg_apply, norm_neg]
        exact h1 }
  refine ⟨R, le_max_right _ _, fun x hx => ?_⟩
  have hle : Γ ≤ B := by
    rw [← hcl]
    refine (Subgroup.closure_le B).2 fun u hu => ?_
    intro v
    have h1 := hC u hu
    rw [Real.norm_eq_abs] at h1
    have h2 : ‖(Multiplicative.toAdd u).2 v‖ ≤ ∑ v : Sf, ‖(Multiplicative.toAdd u).2 v‖ :=
      Finset.single_le_sum (f := fun v : Sf => ‖(Multiplicative.toAdd u).2 v‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_univ v)
    exact h2.trans ((le_abs_self _).trans (h1.trans (le_max_left _ _)))
  exact hle hx

lemma ell_zero {k : Subgroup (Multiplicative (SAdeleRing F Sf))} (hk : IsOpen (annihilator k))
    (ℓ : SAdeleRing F Sf →+ ℝ) (hℓ : Continuous ℓ) (x : Multiplicative (SAdeleRing F Sf))
    (hx : x ∈ k) : ℓ (Multiplicative.toAdd x) = 0 := by
  let χ : ℝ → PontryaginDual (Multiplicative (SAdeleRing F Sf)) := fun t =>
    ({ toFun := fun y => Circle.exp (t * ℓ (Multiplicative.toAdd y))
       map_one' := by
         simp only [toAdd_one, map_zero, mul_zero, Circle.exp_zero]
       map_mul' := by
         intro a b
         simp only [toAdd_mul, map_add, mul_add, Circle.exp_add]
       continuous_toFun := Circle.exp.continuous.comp
         (continuous_const.mul (hℓ.comp continuous_toAdd)) } :
      ContinuousMonoidHom (Multiplicative (SAdeleRing F Sf)) Circle)
  have hχ : Continuous χ := by
    apply ContinuousMonoidHom.continuous_of_continuous_uncurry
    exact Circle.exp.continuous.comp
      (continuous_fst.mul (hℓ.comp (continuous_toAdd.comp continuous_snd)))
  have h0 : χ 0 ∈ annihilator k := by
    intro y _
    show Circle.exp (0 * ℓ (Multiplicative.toAdd y)) = 1
    rw [zero_mul, Circle.exp_zero]
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), χ t ∈ annihilator k :=
    hχ.continuousAt.preimage_mem_nhds (hk.mem_nhds h0)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
  by_contra hne
  generalize hc : ℓ (Multiplicative.toAdd x) = c at hne
  have hcpos : 0 < |c| := abs_pos.mpr hne
  let t : ℝ := min (δ / 2) (1 / (|c| + 1))
  have htpos : 0 < t := lt_min (by linarith) (by positivity)
  have htd : dist t 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos htpos]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have h1 : (χ t) x = 1 := hball htd x hx
  have h2 : Circle.exp (t * c) = 1 := by
    rw [← hc]
    exact h1
  obtain ⟨n, hn⟩ := Circle.exp_eq_one.1 h2
  have h3 : |t * c| < 1 := by
    rw [abs_mul, abs_of_pos htpos]
    have h4 : t ≤ 1 / (|c| + 1) := min_le_right _ _
    have h5 : t * |c| ≤ 1 / (|c| + 1) * |c| := mul_le_mul_of_nonneg_right h4 (abs_nonneg _)
    have h6 : 1 / (|c| + 1) * |c| < 1 := by
      rw [div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]
      linarith
    linarith
  have hn0 : n = 0 := by
    by_contra hn0
    have h7 : (1 : ℝ) ≤ |(n : ℝ)| := by
      have : (1 : ℤ) ≤ |n| := Int.one_le_abs hn0
      exact_mod_cast this
    have h8 : |t * c| = |(n : ℝ)| * (2 * Real.pi) := by
      rw [hn, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    have h9 : (1 : ℝ) * (2 * Real.pi) ≤ |(n : ℝ)| * (2 * Real.pi) :=
      mul_le_mul_of_nonneg_right h7 (by positivity)
    have h10 : (3 : ℝ) < Real.pi := Real.pi_gt_three
    linarith
  rw [hn0, Int.cast_zero, zero_mul] at hn
  have : c = 0 := by
    rcases mul_eq_zero.1 hn with h | h
    · exact absurd h htpos.ne'
    · exact h
  exact hne this

/-- real part of the `w`-coordinate -/
noncomputable def ellRe (w : InfinitePlace F) : SAdeleRing F Sf →+ ℝ where
  toFun y := (InfinitePlace.Completion.extensionEmbedding w (y.1 w)).re
  map_zero' := by
    show (InfinitePlace.Completion.extensionEmbedding w 0).re = 0
    rw [map_zero, Complex.zero_re]
  map_add' a b := by
    show (InfinitePlace.Completion.extensionEmbedding w (a.1 w + b.1 w)).re = _
    rw [map_add, Complex.add_re]

/-- imaginary part of the `w`-coordinate -/
noncomputable def ellIm (w : InfinitePlace F) : SAdeleRing F Sf →+ ℝ where
  toFun y := (InfinitePlace.Completion.extensionEmbedding w (y.1 w)).im
  map_zero' := by
    show (InfinitePlace.Completion.extensionEmbedding w 0).im = 0
    rw [map_zero, Complex.zero_im]
  map_add' a b := by
    show (InfinitePlace.Completion.extensionEmbedding w (a.1 w + b.1 w)).im = _
    rw [map_add, Complex.add_im]

lemma k_inf_zero {k : Subgroup (Multiplicative (SAdeleRing F Sf))} (hk : IsOpen (annihilator k))
    (x : Multiplicative (SAdeleRing F Sf)) (hx : x ∈ k) : (Multiplicative.toAdd x).1 = 0 := by
  funext w
  have hcont : Continuous fun y : SAdeleRing F Sf =>
      InfinitePlace.Completion.extensionEmbedding w (y.1 w) :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp
      ((continuous_apply w).comp continuous_fst)
  have hre := ell_zero hk (ellRe w) (Complex.continuous_re.comp hcont) x hx
  have him := ell_zero hk (ellIm w) (Complex.continuous_im.comp hcont) x hx
  have h : InfinitePlace.Completion.extensionEmbedding w ((Multiplicative.toAdd x).1 w) = 0 :=
    Complex.ext hre him
  exact (map_eq_zero (InfinitePlace.Completion.extensionEmbedding w)).1 h

lemma same_inf {Γ k : Subgroup (Multiplicative (SAdeleRing F Sf))} {m n r s : ℕ} {d : Fin s → ℕ}
    {π : Γ →* Multiplicative (ElemGroup m n r s d)}
    (hk : ∀ x ∈ k, (Multiplicative.toAdd x).1 = 0) (hπ : IsElemPresentation Γ k π)
    (x y : Γ) (h : π x = π y) :
    (Multiplicative.toAdd (x : Multiplicative (SAdeleRing F Sf))).1 =
      (Multiplicative.toAdd (y : Multiplicative (SAdeleRing F Sf))).1 := by
  have h1 : π (x * y⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
  have h2 := hk _ ((hπ.2.2.2.2 _).1 h1)
  have h3 : (Multiplicative.toAdd ((x * y⁻¹ : Γ) : Multiplicative (SAdeleRing F Sf))).1 =
      (Multiplicative.toAdd (x : Multiplicative (SAdeleRing F Sf))).1 -
        (Multiplicative.toAdd (y : Multiplicative (SAdeleRing F Sf))).1 := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, toAdd_mul, toAdd_inv, Prod.fst_add, Prod.fst_neg,
      sub_eq_add_neg]
  rw [h3] at h2
  exact sub_eq_zero.1 h2

lemma inf_bound {Γ k : Subgroup (Multiplicative (SAdeleRing F Sf))} {m n r s : ℕ}
    {d : Fin s → ℕ} {π : Γ →* Multiplicative (ElemGroup m n r s d)}
    (hk : ∀ x ∈ k, (Multiplicative.toAdd x).1 = 0) (hπ : IsElemPresentation Γ k π) :
    ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ ∀ x : Γ,
      infN (Multiplicative.toAdd (x : Multiplicative (SAdeleRing F Sf))).1 ≤
        a * (‖(Multiplicative.toAdd (π x)).1‖ + ‖(Multiplicative.toAdd (π x)).2.2.1‖) + b := by
  have hd := hπ.1
  have hopen := hπ.2.2.1
  have hsurj := hπ.2.2.2.1
  let ι : Γ → ℝ := fun x => infN (Multiplicative.toAdd (x : Multiplicative (SAdeleRing F Sf))).1
  have hι0 : ∀ x, 0 ≤ ι x := fun x => infN_nonneg _
  let E0 : Set (Multiplicative (ElemGroup m n r s d)) :=
    {e | ‖(Multiplicative.toAdd e).1‖ ≤ 1 ∧ (Multiplicative.toAdd e).2.2.1 = 0}
  have hE0 : IsCompact E0 := by
    have : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
    have : ∀ i, NeZero (d i) := fun i => ⟨hd i⟩
    have hK : IsCompact (Metric.closedBall (0 : Fin m → ℝ) 1 ×ˢ
        ((Set.univ : Set (Fin n → UnitAddCircle)) ×ˢ
        (({0} : Set (Fin r → ℤ)) ×ˢ (Set.univ : Set ((i : Fin s) → ZMod (d i)))))) :=
      (isCompact_closedBall _ _).prod (isCompact_univ.prod (isCompact_singleton.prod isCompact_univ))
    have hcl : IsClosed E0 := by
      apply IsClosed.inter
      · exact isClosed_le (continuous_norm.comp (continuous_fst.comp continuous_toAdd))
          continuous_const
      · exact isClosed_eq (continuous_fst.comp (continuous_snd.comp
          (continuous_snd.comp continuous_toAdd))) continuous_const
    refine (hK.image continuous_ofAdd).of_isClosed_subset hcl ?_
    intro e he
    refine ⟨Multiplicative.toAdd e, ⟨mem_closedBall_zero_iff.2 he.1, trivial, he.2, trivial⟩, ?_⟩
    rfl
  let W : Set Γ := {x | ι x < 1}
  have hW : IsOpen W := isOpen_lt (infN_continuous.comp (continuous_fst.comp
    (continuous_toAdd.comp continuous_subtype_val))) continuous_const
  have hW1 : (1 : Γ) ∈ W := by
    show infN (Multiplicative.toAdd ((1 : Γ) : Multiplicative (SAdeleRing F Sf))).1 < 1
    rw [OneMemClass.coe_one, toAdd_one, Prod.fst_zero, infN_zero]
    exact one_pos
  let U : Γ → Set (Multiplicative (ElemGroup m n r s d)) :=
    fun γ => (fun e => π γ * e) '' (π '' W)
  have hU : ∀ γ, IsOpen (U γ) := fun γ => isOpenMap_mul_left (π γ) _ (hopen W hW)
  have hcov : E0 ⊆ ⋃ γ, U γ := by
    intro e _
    obtain ⟨γ, hγ⟩ := hsurj e
    exact Set.mem_iUnion.2 ⟨γ, π 1, ⟨1, hW1, rfl⟩, show π γ * π 1 = e by rw [map_one, mul_one, hγ]⟩
  obtain ⟨t, ht⟩ := hE0.elim_finite_subcover U hU hcov
  let ρ : ℝ := ∑ γ ∈ t, ι γ + 1
  have hρ1 : 1 ≤ ρ := by
    have : 0 ≤ ∑ γ ∈ t, ι γ := Finset.sum_nonneg fun γ _ => hι0 γ
    linarith
  have claim1 : ∀ x : Γ, π x ∈ E0 → ι x ≤ ρ := by
    intro x hx
    have hx' := ht hx
    rw [Set.mem_iUnion₂] at hx'
    obtain ⟨γ, hγt, e', ⟨w, hw, rfl⟩, he'⟩ := hx'
    have hπe : π (γ * w) = π x := by rw [map_mul]; exact he'
    have hs := same_inf hk hπ (γ * w) x hπe
    have hiw : ι w < 1 := hw
    have h1 : ι x ≤ ι γ + ι w := by
      show infN (Multiplicative.toAdd (x : Multiplicative (SAdeleRing F Sf))).1 ≤ _
      rw [← hs, Subgroup.coe_mul, toAdd_mul, Prod.fst_add]
      exact infN_add _ _
    have h2 : ι γ ≤ ∑ γ ∈ t, ι γ := Finset.single_le_sum (fun γ _ => hι0 γ) hγt
    show ι x ≤ ∑ γ ∈ t, ι γ + 1
    linarith
  let β : Fin r → Γ := fun i =>
    (hsurj (Multiplicative.ofAdd ((0, 0, Pi.single i 1, 0) : ElemGroup m n r s d))).choose
  have hβ : ∀ i, π (β i) =
      Multiplicative.ofAdd ((0, 0, Pi.single i 1, 0) : ElemGroup m n r s d) :=
    fun i => (hsurj _).choose_spec
  let bsum : ℝ := ∑ i, ι (β i)
  have hbsum : 0 ≤ bsum := Finset.sum_nonneg fun i _ => hι0 (β i)
  refine ⟨ρ + bsum, 2 * ρ, by linarith, by linarith, fun x => ?_⟩
  generalize he : Multiplicative.toAdd (π x) = e
  let M : ℕ := ⌈‖e.1‖⌉₊
  have hM : (M : ℝ) < ‖e.1‖ + 1 := Nat.ceil_lt_add_one (norm_nonneg _)
  let p : ElemGroup m n r s d := ((M : ℝ)⁻¹ • e.1, 0, 0, 0)
  obtain ⟨γp, hγp⟩ := hsurj (Multiplicative.ofAdd p)
  have hp1 : ‖(M : ℝ)⁻¹ • e.1‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, Nat.abs_cast]
    by_cases hM0 : M = 0
    · rw [hM0, Nat.cast_zero, inv_zero, zero_mul]
      exact zero_le_one
    · have hMpos : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero hM0
      rw [inv_mul_le_iff₀ hMpos, mul_one]
      exact Nat.le_ceil _
  have hγpE : π γp ∈ E0 := by
    rw [hγp]
    exact ⟨hp1, rfl⟩
  have hγpρ : ι γp ≤ ρ := claim1 γp hγpE
  let y : Γ := x * γp ^ (-(M : ℤ)) * ∏ i, β i ^ (-(e.2.2.1 i))
  have hy : Multiplicative.toAdd (π y) =
      e + (-(M : ℤ)) • p +
        ∑ i, (-(e.2.2.1 i)) • ((0, 0, Pi.single i 1, 0) : ElemGroup m n r s d) := by
    simp only [y, map_mul, map_zpow, map_prod, toAdd_mul, toAdd_zpow, toAdd_prod, hβ, hγp, he,
      toAdd_ofAdd]
  have hyE : π y ∈ E0 := by
    constructor
    · rw [hy, Prod.fst_add, Prod.fst_add, Prod.fst_sum, Prod.smul_fst]
      have h0 : ∑ i, ((-(e.2.2.1 i)) • ((0, 0, Pi.single i 1, 0) : ElemGroup m n r s d)).1 = 0 :=
        Finset.sum_eq_zero fun i _ => by rw [Prod.smul_fst, smul_zero]
      rw [h0, add_zero]
      show ‖e.1 + (-(M : ℤ)) • ((M : ℝ)⁻¹ • e.1)‖ ≤ 1
      by_cases hM0 : M = 0
      · have he1 : ‖e.1‖ ≤ 0 := Nat.ceil_eq_zero.1 hM0
        have he2 : e.1 = 0 := norm_le_zero_iff.1 he1
        rw [he2, smul_zero, smul_zero, add_zero, norm_zero]
        exact zero_le_one
      · have hMne : (M : ℝ) ≠ 0 := by exact_mod_cast hM0
        rw [neg_smul, ← Int.cast_smul_eq_zsmul ℝ, smul_smul, Int.cast_natCast,
          mul_inv_cancel₀ hMne, one_smul, add_neg_cancel, norm_zero]
        exact zero_le_one
    · rw [hy]
      funext j
      have h1 : ((e + (-(M : ℤ)) • p +
          ∑ i, (-(e.2.2.1 i)) • ((0, 0, Pi.single i 1, 0) : ElemGroup m n r s d)).2.2.1) j =
          e.2.2.1 j + (-(M : ℤ)) * 0 + ∑ i, (-(e.2.2.1 i)) * ((Pi.single i (1 : ℤ) : Fin r → ℤ) j) := by
        simp only [Prod.snd_add, Prod.fst_add, Prod.snd_sum, Prod.fst_sum, Prod.smul_snd,
          Prod.smul_fst, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, p,
          Pi.zero_apply]
      rw [h1]
      simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Pi.zero_apply, add_zero]
      rw [Finset.sum_ite_eq]
      simp
  have hyρ : ι y ≤ ρ := claim1 y hyE
  have hx : (Multiplicative.toAdd (x : Multiplicative (SAdeleRing F Sf))).1 =
      (Multiplicative.toAdd (y : Multiplicative (SAdeleRing F Sf))).1 +
        (M : ℤ) • (Multiplicative.toAdd (γp : Multiplicative (SAdeleRing F Sf))).1 +
        ∑ i, (e.2.2.1 i) • (Multiplicative.toAdd (β i : Multiplicative (SAdeleRing F Sf))).1 := by
    simp only [y, Subgroup.coe_mul, Subgroup.coe_zpow, SubmonoidClass.coe_finsetProd, toAdd_mul,
      toAdd_zpow, toAdd_prod, neg_smul, Prod.fst_add, Prod.fst_neg, Prod.fst_sum, Prod.smul_fst,
      Finset.sum_neg_distrib]
    abel
  have hz : ∀ i, |((e.2.2.1 i : ℤ) : ℝ)| ≤ ‖e.2.2.1‖ := by
    intro i
    have := norm_le_pi_norm e.2.2.1 i
    rw [Int.norm_eq_abs] at this
    exact this
  have hsum : infN (∑ i, (e.2.2.1 i) •
      (Multiplicative.toAdd (β i : Multiplicative (SAdeleRing F Sf))).1) ≤ ‖e.2.2.1‖ * bsum := by
    refine (infN_sum _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => (infN_zsmul _ _).trans ?_
    exact mul_le_mul_of_nonneg_right (hz i) (hι0 _)
  have hMz : infN ((M : ℤ) • (Multiplicative.toAdd (γp : Multiplicative (SAdeleRing F Sf))).1) ≤
      (M : ℝ) * ρ := by
    refine (infN_zsmul _ _).trans ?_
    rw [Int.cast_natCast, Nat.abs_cast]
    exact mul_le_mul_of_nonneg_left hγpρ (Nat.cast_nonneg _)
  show ι x ≤ _
  have hxι : ι x ≤ ι y + (M : ℝ) * ρ + ‖e.2.2.1‖ * bsum := by
    show infN _ ≤ _
    rw [hx]
    refine (infN_add _ _).trans ?_
    exact add_le_add ((infN_add _ _).trans (add_le_add le_rfl hMz)) hsum
  have hMρ : (M : ℝ) * ρ ≤ (‖e.1‖ + 1) * ρ := mul_le_mul_of_nonneg_right hM.le (by linarith)
  have hn1 : 0 ≤ ‖e.1‖ := norm_nonneg _
  have hn2 : 0 ≤ ‖e.2.2.1‖ := norm_nonneg _
  nlinarith

lemma stage {Γ k : Subgroup (Multiplicative (SAdeleRing F Sf))} {m n r s : ℕ}
    {d : Fin s → ℕ} {π : Γ →* Multiplicative (ElemGroup m n r s d)}
    (hs : IsStructuralPair Γ k) (hπ : IsElemPresentation Γ k π) :
    ∃ R a b : ℝ, 0 ≤ R ∧ 0 ≤ a ∧ 0 ≤ b ∧
      (∀ x ∈ Γ, ∀ v : Sf, ‖(Multiplicative.toAdd x).2 v‖ ≤ R) ∧ ∀ x : Γ,
      infN (Multiplicative.toAdd (x : Multiplicative (SAdeleRing F Sf))).1 ≤
        a * (‖(Multiplicative.toAdd (π x)).1‖ + ‖(Multiplicative.toAdd (π x)).2.2.1‖) + b := by
  obtain ⟨R, hR0, hR⟩ := fin_bdd hs.2.1
  obtain ⟨a, b, ha, hb, hab⟩ := inf_bound (k_inf_zero hs.2.2.1.2.1) hπ
  exact ⟨R, a, b, hR0, ha, hb, hR, hab⟩

end Struct

section Elem

variable {m n r s : ℕ} {d : Fin s → ℕ}

/-- weighted pointwise bounds on the elementary group -/
def EB (h : ElemGroup m n r s d → ℂ) : Prop :=
  ∀ i j : ℕ, ∃ C : ℝ, ∀ e : ElemGroup m n r s d, ‖e.2.2.1‖ ^ j * ‖e.1‖ ^ i * ‖h e‖ ≤ C

lemma lift_circle (z : Fin n → UnitAddCircle) :
    ∃ t : Fin n → ℝ, (fun l => ((t l : ℝ) : UnitAddCircle)) = z :=
  ⟨fun l => Classical.choose (QuotientAddGroup.mk_surjective (z l)),
    funext fun l => Classical.choose_spec (QuotientAddGroup.mk_surjective (z l))⟩

lemma elemLift_eq (h : ElemGroup m n r s d → ℂ) (e : ElemGroup m n r s d) (t : Fin n → ℝ)
    (ht : (fun l => ((t l : ℝ) : UnitAddCircle)) = e.2.1) :
    elemLift h e.2.2.1 e.2.2.2 (e.1, t) = h e := by
  unfold elemLift
  rw [ht]

lemma eb_of_rapid (h : ElemGroup m n r s d → ℂ) (hh : IsRapidDecay h) : EB h := by
  intro i j
  obtain ⟨C, hC⟩ := hh.2 i j 0
  refine ⟨C, fun e => ?_⟩
  obtain ⟨t, ht⟩ := lift_circle e.2.1
  have h1 := hC e.2.2.1 e.2.2.2 (e.1, t)
  rw [norm_iteratedFDeriv_zero, elemLift_eq h e t ht] at h1
  exact h1

lemma eb_add (h₁ h₂ : ElemGroup m n r s d → ℂ) (h1 : EB h₁) (h2 : EB h₂) : EB (h₁ + h₂) := by
  intro i j
  obtain ⟨C₁, hC₁⟩ := h1 i j
  obtain ⟨C₂, hC₂⟩ := h2 i j
  refine ⟨C₁ + C₂, fun e => ?_⟩
  have hw : 0 ≤ ‖e.2.2.1‖ ^ j * ‖e.1‖ ^ i := by positivity
  have h3 : ‖(h₁ + h₂) e‖ ≤ ‖h₁ e‖ + ‖h₂ e‖ := norm_add_le _ _
  calc ‖e.2.2.1‖ ^ j * ‖e.1‖ ^ i * ‖(h₁ + h₂) e‖
      ≤ ‖e.2.2.1‖ ^ j * ‖e.1‖ ^ i * (‖h₁ e‖ + ‖h₂ e‖) := mul_le_mul_of_nonneg_left h3 hw
    _ = ‖e.2.2.1‖ ^ j * ‖e.1‖ ^ i * ‖h₁ e‖ + ‖e.2.2.1‖ ^ j * ‖e.1‖ ^ i * ‖h₂ e‖ := by ring
    _ ≤ C₁ + C₂ := add_le_add (hC₁ e) (hC₂ e)

lemma eb_smul (c : ℂ) (h : ElemGroup m n r s d → ℂ) (h1 : EB h) : EB (c • h) := by
  intro i j
  obtain ⟨C, hC⟩ := h1 i j
  refine ⟨‖c‖ * C, fun e => ?_⟩
  have h3 : ‖(c • h) e‖ = ‖c‖ * ‖h e‖ := by rw [Pi.smul_apply, smul_eq_mul, norm_mul]
  rw [h3]
  have := mul_le_mul_of_nonneg_left (hC e) (norm_nonneg c)
  calc ‖e.2.2.1‖ ^ j * ‖e.1‖ ^ i * (‖c‖ * ‖h e‖)
      = ‖c‖ * (‖e.2.2.1‖ ^ j * ‖e.1‖ ^ i * ‖h e‖) := by ring
    _ ≤ ‖c‖ * C := this

lemma eb_zero : EB (0 : ElemGroup m n r s d → ℂ) := by
  intro i j
  exact ⟨0, fun e => by rw [Pi.zero_apply, norm_zero, mul_zero]⟩

lemma cont_of_rapid (h : ElemGroup m n r s d → ℂ) (hh : IsRapidDecay h) : Continuous h := by
  let Λ : (Fin m → ℝ) × (Fin n → ℝ) × (Fin r → ℤ) × ((i : Fin s) → ZMod (d i)) →
      ElemGroup m n r s d :=
    Prod.map id (Prod.map (Pi.map fun _ => (QuotientAddGroup.mk : ℝ → UnitAddCircle)) id)
  have hΛc : Continuous Λ := continuous_id.prodMap
    ((continuous_pi fun l => (continuous_quotient_mk'.comp (continuous_apply l))).prodMap
      continuous_id)
  have hΛo : IsOpenMap Λ := IsOpenMap.id.prodMap ((IsOpenMap.piMap
    (fun _ => QuotientAddGroup.isOpenMap_coe)
    (Filter.Eventually.of_forall fun _ => QuotientAddGroup.mk_surjective)).prodMap IsOpenMap.id)
  have hΛs : Function.Surjective Λ := by
    intro e
    obtain ⟨t, ht⟩ := lift_circle e.2.1
    refine ⟨⟨e.1, t, e.2.2.1, e.2.2.2⟩, ?_⟩
    show (e.1, (fun l => ((t l : ℝ) : UnitAddCircle)), e.2.2.1, e.2.2.2) = e
    rw [ht]
  have hq : Topology.IsQuotientMap Λ := hΛo.isQuotientMap hΛc hΛs
  rw [hq.continuous_iff]
  rw [continuous_iff_continuousAt]
  intro q₀
  have hS : {q : (Fin m → ℝ) × (Fin n → ℝ) × (Fin r → ℤ) × ((i : Fin s) → ZMod (d i)) |
      q.2.2.1 = q₀.2.2.1 ∧ q.2.2.2 = q₀.2.2.2} ∈ 𝓝 q₀ := by
    refine IsOpen.mem_nhds ?_ (show q₀.2.2.1 = q₀.2.2.1 ∧ q₀.2.2.2 = q₀.2.2.2 from ⟨rfl, rfl⟩)
    apply IsOpen.inter
    · exact (isOpen_discrete {q₀.2.2.1}).preimage
        (continuous_fst.comp (continuous_snd.comp continuous_snd))
    · exact (isOpen_discrete {q₀.2.2.2}).preimage
        (continuous_snd.comp (continuous_snd.comp continuous_snd))
  have hc : Continuous fun q : (Fin m → ℝ) × (Fin n → ℝ) × (Fin r → ℤ) ×
      ((i : Fin s) → ZMod (d i)) => elemLift h q₀.2.2.1 q₀.2.2.2 (q.1, q.2.1) :=
    (hh.1 q₀.2.2.1 q₀.2.2.2).continuous.comp (continuous_fst.prodMk
      (continuous_fst.comp continuous_snd))
  refine hc.continuousAt.congr ?_
  filter_upwards [hS] with q hq'
  show elemLift h q₀.2.2.1 q₀.2.2.2 (q.1, q.2.1) = h (Λ q)
  unfold elemLift
  rw [← hq'.1, ← hq'.2]
  rfl

lemma eb_fun (φ : ElemGroup m n r s d → ℂ) (hg : φ ∈ elemSchwartzSubmodule m n r s d) :
    EB φ ∧ Continuous φ := by
  induction hg using Submodule.span_induction with
  | mem x hx => exact ⟨eb_of_rapid x hx, cont_of_rapid x hx⟩
  | zero => exact ⟨eb_zero, continuous_const⟩
  | add x y _ _ hx hy => exact ⟨eb_add x y hx.1 hy.1, hx.2.add hy.2⟩
  | smul c x _ hx => exact ⟨eb_smul c x hx.1, hx.2.const_smul c⟩

lemma eb_elem (g : ElemSchwartz m n r s d) : EB g.toFun ∧ Continuous g.toFun :=
  eb_fun g.1 g.2

end Elem

section Pull

lemma one_add_pow_le (u : ℝ) (hu : 0 ≤ u) (N : ℕ) : (1 + u) ^ N ≤ 2 ^ N * (1 + u ^ N) := by
  have hN : 0 ≤ u ^ N := pow_nonneg hu N
  by_cases h : u ≤ 1
  · have h1 : (1 + u) ^ N ≤ 2 ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
    have h2 : (2 : ℝ) ^ N ≤ 2 ^ N * (1 + u ^ N) := by
      have : (0 : ℝ) ≤ 2 ^ N := by positivity
      nlinarith
    linarith
  · push Not at h
    have h1 : (1 + u) ^ N ≤ (2 * u) ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
    rw [mul_pow] at h1
    have h2 : (2 : ℝ) ^ N * u ^ N ≤ 2 ^ N * (1 + u ^ N) := by
      have : (0 : ℝ) ≤ 2 ^ N := by positivity
      nlinarith
    linarith

lemma pull_bound (X u v a b D : ℝ) (N : ℕ) (hX : 0 ≤ X) (hu : 0 ≤ u) (hv : 0 ≤ v) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hXab : X ≤ a * (u + v) + b) (y : ℝ) (hy : 0 ≤ y)
    (h00 : v ^ 0 * u ^ 0 * y ≤ D) (hN0 : v ^ 0 * u ^ N * y ≤ D) (h0N : v ^ N * u ^ 0 * y ≤ D)
    (hNN : v ^ N * u ^ N * y ≤ D) :
    (1 + X) ^ N * y ≤ (1 + a + b) ^ N * 4 ^ N * (4 * D) := by
  simp only [pow_zero, one_mul, mul_one] at h00 hN0 h0N
  have h1 : 1 + X ≤ (1 + a + b) * ((1 + u) * (1 + v)) := by
    have key : (1 + a + b) * ((1 + u) * (1 + v)) = 1 + a * (u + v) + b +
        (u + v + u * v + a + a * u * v + b * (u + v + u * v)) := by ring
    have hpos : 0 ≤ u + v + u * v + a + a * u * v + b * (u + v + u * v) := by positivity
    rw [key]
    linarith
  have h2 : (1 + X) ^ N ≤ ((1 + a + b) * ((1 + u) * (1 + v))) ^ N :=
    pow_le_pow_left₀ (by linarith) h1 N
  rw [mul_pow, mul_pow] at h2
  have h3 := one_add_pow_le u hu N
  have h4 := one_add_pow_le v hv N
  have hP : 0 ≤ (1 + a + b) ^ N := by positivity
  have hU : 0 ≤ (1 + u) ^ N := by positivity
  have hV : 0 ≤ (1 + v) ^ N := by positivity
  have h5 : (1 + u) ^ N * (1 + v) ^ N ≤ (2 ^ N * (1 + u ^ N)) * (2 ^ N * (1 + v ^ N)) :=
    mul_le_mul h3 h4 hV (by positivity)
  have h6 : (1 + u ^ N) * (1 + v ^ N) * y ≤ 4 * D := by
    have e : (1 + u ^ N) * (1 + v ^ N) * y = y + u ^ N * y + v ^ N * y + v ^ N * u ^ N * y := by
      ring
    rw [e]
    linarith
  have h4N : (4 : ℝ) ^ N = 2 ^ N * 2 ^ N := by
    rw [← mul_pow]
    norm_num
  calc (1 + X) ^ N * y ≤ (1 + a + b) ^ N * ((1 + u) ^ N * (1 + v) ^ N) * y :=
        mul_le_mul_of_nonneg_right h2 hy
    _ ≤ (1 + a + b) ^ N * ((2 ^ N * (1 + u ^ N)) * (2 ^ N * (1 + v ^ N))) * y :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h5 hP) hy
    _ = (1 + a + b) ^ N * 4 ^ N * ((1 + u ^ N) * (1 + v ^ N) * y) := by rw [h4N]; ring
    _ ≤ (1 + a + b) ^ N * 4 ^ N * (4 * D) :=
        mul_le_mul_of_nonneg_left h6 (by positivity)

end Pull

section Good

variable {F : Type*} [Field F] [NumberField F] {Sf : Finset (HeightOneSpectrum (𝓞 F))}

/-- support at the finite places of `S` is bounded, rapid decay at the infinite places,
continuity -/
def GoodF (ψ : Multiplicative (SAdeleRing F Sf) → ℂ) : Prop :=
  (∃ R : ℝ, ∀ x, ψ x ≠ 0 → ∀ v : Sf, ‖(Multiplicative.toAdd x).2 v‖ ≤ R) ∧
  (∀ N : ℕ, ∃ C : ℝ, ∀ x, (1 + infN (Multiplicative.toAdd x).1) ^ N * ‖ψ x‖ ≤ C) ∧
  Continuous ψ

lemma goodF_zero : GoodF (0 : Multiplicative (SAdeleRing F Sf) → ℂ) :=
  ⟨⟨0, fun x hx => absurd rfl hx⟩,
    fun N => ⟨0, fun x => by rw [Pi.zero_apply, norm_zero, mul_zero]⟩, continuous_const⟩

lemma goodF_add (ψ₁ ψ₂ : Multiplicative (SAdeleRing F Sf) → ℂ) (h1 : GoodF ψ₁)
    (h2 : GoodF ψ₂) : GoodF (ψ₁ + ψ₂) := by
  obtain ⟨⟨R₁, hR₁⟩, hD₁, hc₁⟩ := h1
  obtain ⟨⟨R₂, hR₂⟩, hD₂, hc₂⟩ := h2
  refine ⟨⟨max R₁ R₂, fun x hx v => ?_⟩, fun N => ?_, hc₁.add hc₂⟩
  · by_cases h : ψ₁ x = 0
    · have h' : ψ₂ x ≠ 0 := by
        intro h'
        apply hx
        rw [Pi.add_apply, h, h', add_zero]
      exact (hR₂ x h' v).trans (le_max_right _ _)
    · exact (hR₁ x h v).trans (le_max_left _ _)
  · obtain ⟨C₁, hC₁⟩ := hD₁ N
    obtain ⟨C₂, hC₂⟩ := hD₂ N
    refine ⟨C₁ + C₂, fun x => ?_⟩
    have hw : 0 ≤ (1 + infN (Multiplicative.toAdd x).1) ^ N :=
      pow_nonneg (by linarith [infN_nonneg (Multiplicative.toAdd x).1]) N
    have h3 : ‖(ψ₁ + ψ₂) x‖ ≤ ‖ψ₁ x‖ + ‖ψ₂ x‖ := norm_add_le _ _
    calc (1 + infN (Multiplicative.toAdd x).1) ^ N * ‖(ψ₁ + ψ₂) x‖
        ≤ (1 + infN (Multiplicative.toAdd x).1) ^ N * (‖ψ₁ x‖ + ‖ψ₂ x‖) :=
          mul_le_mul_of_nonneg_left h3 hw
      _ = (1 + infN (Multiplicative.toAdd x).1) ^ N * ‖ψ₁ x‖ +
          (1 + infN (Multiplicative.toAdd x).1) ^ N * ‖ψ₂ x‖ := by ring
      _ ≤ C₁ + C₂ := add_le_add (hC₁ x) (hC₂ x)

lemma goodF_smul (c : ℂ) (ψ : Multiplicative (SAdeleRing F Sf) → ℂ) (h : GoodF ψ) :
    GoodF (c • ψ) := by
  obtain ⟨⟨R, hR⟩, hD, hc⟩ := h
  refine ⟨⟨R, fun x hx v => ?_⟩, fun N => ?_, hc.const_smul c⟩
  · have h' : ψ x ≠ 0 := by
      intro h'
      apply hx
      rw [Pi.smul_apply, h', smul_zero]
    exact hR x h' v
  · obtain ⟨C, hC⟩ := hD N
    refine ⟨‖c‖ * C, fun x => ?_⟩
    have h3 : ‖(c • ψ) x‖ = ‖c‖ * ‖ψ x‖ := by rw [Pi.smul_apply, smul_eq_mul, norm_mul]
    rw [h3]
    have := mul_le_mul_of_nonneg_left (hC x) (norm_nonneg c)
    calc (1 + infN (Multiplicative.toAdd x).1) ^ N * (‖c‖ * ‖ψ x‖)
        = ‖c‖ * ((1 + infN (Multiplicative.toAdd x).1) ^ N * ‖ψ x‖) := by ring
      _ ≤ ‖c‖ * C := this

lemma extendPullback_of_mem {Γ : Subgroup (Multiplicative (SAdeleRing F Sf))} {m n r s : ℕ}
    {d : Fin s → ℕ} (π : Γ →* Multiplicative (ElemGroup m n r s d))
    (h : ElemGroup m n r s d → ℂ) (x : Multiplicative (SAdeleRing F Sf)) (hx : x ∈ Γ) :
    extendPullback Γ π h x = h (Multiplicative.toAdd (π ⟨x, hx⟩)) := by
  unfold extendPullback
  rw [dif_pos hx]

lemma extendPullback_of_not_mem {Γ : Subgroup (Multiplicative (SAdeleRing F Sf))} {m n r s : ℕ}
    {d : Fin s → ℕ} (π : Γ →* Multiplicative (ElemGroup m n r s d))
    (h : ElemGroup m n r s d → ℂ) (x : Multiplicative (SAdeleRing F Sf)) (hx : x ∉ Γ) :
    extendPullback Γ π h x = 0 := by
  unfold extendPullback
  rw [dif_neg hx]

/-- the four weighted bounds used for the pull-back estimate -/
lemma four_bounds {m n r s : ℕ} {d : Fin s → ℕ} (h : ElemGroup m n r s d → ℂ) (hh : EB h)
    (N : ℕ) : ∃ D : ℝ, 0 ≤ D ∧ ∀ e : ElemGroup m n r s d,
      ‖e.2.2.1‖ ^ 0 * ‖e.1‖ ^ 0 * ‖h e‖ ≤ D ∧ ‖e.2.2.1‖ ^ 0 * ‖e.1‖ ^ N * ‖h e‖ ≤ D ∧
      ‖e.2.2.1‖ ^ N * ‖e.1‖ ^ 0 * ‖h e‖ ≤ D ∧ ‖e.2.2.1‖ ^ N * ‖e.1‖ ^ N * ‖h e‖ ≤ D := by
  obtain ⟨C1, hC1⟩ := hh 0 0
  obtain ⟨C2, hC2⟩ := hh N 0
  obtain ⟨C3, hC3⟩ := hh 0 N
  obtain ⟨C4, hC4⟩ := hh N N
  refine ⟨max (max (max C1 C2) (max C3 C4)) 0, le_max_right _ _, fun e => ⟨?_, ?_, ?_, ?_⟩⟩
  · exact (hC1 e).trans ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _)))
  · exact (hC2 e).trans ((le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _)))
  · exact (hC3 e).trans ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_left _ _)))
  · exact (hC4 e).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_left _ _)))

lemma gen_decay {Γ k : Subgroup (Multiplicative (SAdeleRing F Sf))} {m n r s : ℕ}
    {d : Fin s → ℕ} {π : Γ →* Multiplicative (ElemGroup m n r s d)} (a b : ℝ) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hab : ∀ x : Γ,
      infN (Multiplicative.toAdd (x : Multiplicative (SAdeleRing F Sf))).1 ≤
        a * (‖(Multiplicative.toAdd (π x)).1‖ + ‖(Multiplicative.toAdd (π x)).2.2.1‖) + b)
    (h : ElemGroup m n r s d → ℂ) (N : ℕ) (D : ℝ) (hD0 : 0 ≤ D)
    (hD : ∀ e : ElemGroup m n r s d,
      ‖e.2.2.1‖ ^ 0 * ‖e.1‖ ^ 0 * ‖h e‖ ≤ D ∧ ‖e.2.2.1‖ ^ 0 * ‖e.1‖ ^ N * ‖h e‖ ≤ D ∧
      ‖e.2.2.1‖ ^ N * ‖e.1‖ ^ 0 * ‖h e‖ ≤ D ∧ ‖e.2.2.1‖ ^ N * ‖e.1‖ ^ N * ‖h e‖ ≤ D)
    (x : Multiplicative (SAdeleRing F Sf)) :
    (1 + infN (Multiplicative.toAdd x).1) ^ N * ‖extendPullback Γ π h x‖ ≤
      (1 + a + b) ^ N * 4 ^ N * (4 * D) := by
  by_cases hxΓ : x ∈ Γ
  · rw [extendPullback_of_mem π h x hxΓ]
    obtain ⟨h1, h2, h3, h4⟩ := hD (Multiplicative.toAdd (π ⟨x, hxΓ⟩))
    exact pull_bound _ _ _ a b D N (infN_nonneg _) (norm_nonneg _) (norm_nonneg _) ha hb
      (hab ⟨x, hxΓ⟩) _ (norm_nonneg _) h1 h2 h3 h4
  · rw [extendPullback_of_not_mem π h x hxΓ, norm_zero, mul_zero]
    positivity

lemma goodF_gen {Γ k : Subgroup (Multiplicative (SAdeleRing F Sf))} {m n r s : ℕ}
    {d : Fin s → ℕ} {π : Γ →* Multiplicative (ElemGroup m n r s d)}
    (hs : IsStructuralPair Γ k) (hπ : IsElemPresentation Γ k π) (g : ElemSchwartz m n r s d) :
    GoodF (extendPullback Γ π g.toFun) := by
  obtain ⟨R, a, b, hR0, ha, hb, hR, hab⟩ := stage hs hπ
  obtain ⟨heb, hgc⟩ := eb_elem g
  refine ⟨⟨R, fun x hx v => ?_⟩, fun N => ?_, ?_⟩
  · by_cases hxΓ : x ∈ Γ
    · exact hR x hxΓ v
    · exact absurd (extendPullback_of_not_mem π g.toFun x hxΓ) hx
  · obtain ⟨D, hD0, hD⟩ := four_bounds g.toFun heb N
    exact ⟨_, gen_decay (k := k) a b ha hb hab g.toFun N D hD0 hD⟩
  · rw [continuous_iff_continuousAt]
    intro x
    by_cases hxΓ : x ∈ Γ
    · have hemb : Topology.IsOpenEmbedding
          (Subtype.val : Γ → Multiplicative (SAdeleRing F Sf)) := hs.1.isOpenEmbedding_subtypeVal
      have heq : extendPullback Γ π g.toFun ∘ Subtype.val =
          fun y : Γ => g.toFun (Multiplicative.toAdd (π y)) := by
        funext y
        exact extendPullback_of_mem π g.toFun y.1 y.2
      have h1 : ContinuousAt (extendPullback Γ π g.toFun ∘ Subtype.val) ⟨x, hxΓ⟩ := by
        rw [heq]
        exact (hgc.comp (continuous_toAdd.comp hπ.2.1)).continuousAt
      exact hemb.continuousAt_iff.1 h1
    · have hcl : IsClosed (Γ : Set (Multiplicative (SAdeleRing F Sf))) :=
        Subgroup.isClosed_of_isOpen Γ hs.1
      have hev : ∀ᶠ y in 𝓝 x, y ∉ Γ := hcl.isOpen_compl.mem_nhds hxΓ
      refine (continuousAt_const (y := (0 : ℂ))).congr ?_
      filter_upwards [hev] with y hy
      exact (extendPullback_of_not_mem π g.toFun y hy).symm

lemma goodF_fun (φ : Multiplicative (SAdeleRing F Sf) → ℂ)
    (hφ : φ ∈ schwartzBruhatSubmodule (Multiplicative (SAdeleRing F Sf))) : GoodF φ := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨Γ, k, m, n, r, s, d, π, g, hs, hπ, rfl⟩ := hx
    exact goodF_gen hs hπ g
  | zero => exact goodF_zero
  | add x y _ _ hx hy => exact goodF_add x y hx hy
  | smul c x _ hx => exact goodF_smul c x hx

lemma goodF_sb (f : SAdelicSchwartz F Sf) : GoodF f.toFun := goodF_fun f.1 f.2

/-- the domination properties of `f.eval` -/
lemma eval_good (f : SAdelicSchwartz F Sf) :
    (∃ R : ℝ, ∀ x : SAdeleRing F Sf, f.eval x ≠ 0 → ∀ v : Sf, ‖x.2 v‖ ≤ R) ∧
    (∀ N : ℕ, ∃ C : ℝ, ∀ x : SAdeleRing F Sf, (1 + infN x.1) ^ N * ‖f.eval x‖ ≤ C) ∧
    Continuous f.eval := by
  obtain ⟨⟨R, hR⟩, hD, hc⟩ := goodF_sb f
  refine ⟨⟨R, fun x hx v => hR (Multiplicative.ofAdd x) hx v⟩, fun N => ?_,
    hc.comp continuous_ofAdd⟩
  obtain ⟨C, hC⟩ := hD N
  exact ⟨C, fun x => hC (Multiplicative.ofAdd x)⟩

end Good

section Count

variable {F : Type*} [Field F] [NumberField F] {Sf : Finset (HeightOneSpectrum (𝓞 F))}

/-- the rank exponent `r₁ + r₂ + |S_f| - 1` -/
noncomputable abbrev rk (F : Type*) [Field F] [NumberField F] (Sf : Finset (HeightOneSpectrum (𝓞 F))) : ℕ :=
  InfinitePlace.nrRealPlaces F + InfinitePlace.nrComplexPlaces F + Sf.card - 1

/-- the degree `∑ mult w` -/
noncomputable def nn (F : Type*) [Field F] [NumberField F] : ℕ :=
  ∑ w : InfinitePlace F, w.mult

lemma one_le_nn : 1 ≤ nn F := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have h1 : w.mult ≤ nn F :=
    Finset.single_le_sum (f := fun w : InfinitePlace F => w.mult) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ w)
  have h2 : 0 < w.mult := InfinitePlace.mult_pos
  omega

/-- the unit box of `A.4.1.1` -/
def boxS (Sf : Finset (HeightOneSpectrum (𝓞 F))) (h : SIdeleGroup F Sf) : Set Fˣ :=
  {ξ : Fˣ | ξ ∈ SUnits Sf ∧
    (∀ w : InfinitePlace F, ‖(sDiagonal Sf (ξ : F) * (h : SAdeleRing F Sf)).1 w‖ ≤ 1) ∧
    ∀ v : Sf, (sDiagonal Sf (ξ : F) * (h : SAdeleRing F Sf)).2 v ∈
      (v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F}

/-- the `S`-idele with infinite components `c` and finite components `d` -/
noncomputable def mkId (c d : Fˣ) : SIdeleGroup F Sf where
  val := ((sDiagonal Sf (c : F)).1, (sDiagonal Sf (d : F)).2)
  inv := ((sDiagonal Sf ((c⁻¹ : Fˣ) : F)).1, (sDiagonal Sf ((d⁻¹ : Fˣ) : F)).2)
  val_inv := by
    refine Prod.ext ?_ ?_
    · show (sDiagonal Sf (c : F)).1 * (sDiagonal Sf ((c⁻¹ : Fˣ) : F)).1 =
        (1 : SAdeleRing F Sf).1
      rw [← Prod.fst_mul, ← map_mul, Units.mul_inv, map_one]
    · show (sDiagonal Sf (d : F)).2 * (sDiagonal Sf ((d⁻¹ : Fˣ) : F)).2 =
        (1 : SAdeleRing F Sf).2
      rw [← Prod.snd_mul, ← map_mul, Units.mul_inv, map_one]
  inv_val := by
    refine Prod.ext ?_ ?_
    · show (sDiagonal Sf ((c⁻¹ : Fˣ) : F)).1 * (sDiagonal Sf (c : F)).1 =
        (1 : SAdeleRing F Sf).1
      rw [← Prod.fst_mul, ← map_mul, Units.inv_mul, map_one]
    · show (sDiagonal Sf ((d⁻¹ : Fˣ) : F)).2 * (sDiagonal Sf (d : F)).2 =
        (1 : SAdeleRing F Sf).2
      rw [← Prod.snd_mul, ← map_mul, Units.inv_mul, map_one]

lemma mkId_fst (c d : Fˣ) (g : SIdeleGroup F Sf) :
    ((mkId c d * g : SIdeleGroup F Sf) : SAdeleRing F Sf).1 =
      (sDiagonal Sf (c : F) * (g : SAdeleRing F Sf)).1 := rfl

lemma mkId_snd (c d : Fˣ) (g : SIdeleGroup F Sf) :
    ((mkId c d * g : SIdeleGroup F Sf) : SAdeleRing F Sf).2 =
      (sDiagonal Sf (d : F) * (g : SAdeleRing F Sf)).2 := rfl

lemma norm_diag_inf (x : F) (y : SAdeleRing F Sf) (w : InfinitePlace F) :
    ‖(sDiagonal Sf x * y).1 w‖ = w x * ‖y.1 w‖ := by
  change ‖(x : w.Completion) * y.1 w‖ = _
  rw [norm_mul, inf_norm_coe]

lemma norm_diag_fin (x : F) (y : SAdeleRing F Sf) (v : Sf) :
    ‖(sDiagonal Sf x * y).2 v‖ =
      ‖(x : (v : HeightOneSpectrum (𝓞 F)).adicCompletion F)‖ * ‖y.2 v‖ := by
  change ‖(x : (v : HeightOneSpectrum (𝓞 F)).adicCompletion F) * y.2 v‖ = _
  rw [norm_mul]

lemma diag_mul_assoc (x y : F) (z : SAdeleRing F Sf) :
    sDiagonal Sf x * (sDiagonal Sf y * z) = sDiagonal Sf (x * y) * z := by
  rw [map_mul, mul_assoc]

lemma fin_coe_one' (v : HeightOneSpectrum (𝓞 F)) :
    ((1 : F) : v.adicCompletion F) = 1 :=
  map_one (FinitePlace.embedding v)

lemma norm_mkId (c d : Fˣ) (g : SIdeleGroup F Sf) :
    sIdeleNorm Sf (mkId c d * g) = (∏ w : InfinitePlace F, w (c : F) ^ w.mult) *
      (∏ v : Sf, ‖((d : F) : (v : HeightOneSpectrum (𝓞 F)).adicCompletion F)‖) *
        sIdeleNorm Sf g := by
  unfold sIdeleNorm
  rw [mkId_fst, mkId_snd]
  simp only [norm_diag_inf, norm_diag_fin, mul_pow, Finset.prod_mul_distrib]
  ring

lemma norm_le_one_of_box (h : SIdeleGroup F Sf) (ξ : Fˣ) (hξ : ξ ∈ boxS Sf h) :
    sIdeleNorm Sf h ≤ 1 := by
  have h1 := box_le Sf h ξ hξ.2.1 hξ.2.2
  have h2 : ∑ i, (lam Sf ξ i + gam Sf h i) ≤ 0 := Finset.sum_nonpos fun i _ => h1 i
  rw [Finset.sum_add_distrib, sum_lam Sf ξ hξ.1, sum_gam, zero_add] at h2
  exact (Real.log_nonpos_iff (sIdeleNorm_pos Sf h).le).1 h2

lemma count_all : ∃ C K₀ : ℝ, 0 < C ∧ 0 ≤ K₀ ∧ ∀ h : SIdeleGroup F Sf,
    (boxS Sf h).Finite ∧
      ((boxS Sf h).ncard : ℝ) ≤ C * (|Real.log (sIdeleNorm Sf h)| + K₀) ^ rk F Sf := by
  obtain ⟨C, ε, hC, hε, hcount⟩ := count_bound Sf
  obtain ⟨i, hi⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
  let c : Fˣ := (Units.mk0 (2 : F) two_ne_zero)⁻¹ ^ i
  have hwc : ∀ w : InfinitePlace F, w (c : F) = (1 / 2 : ℝ) ^ i := by
    intro w
    have h2 : w (2 : F) = 2 := by
      have := InfinitePlace.map_natCast w 2
      exact_mod_cast this
    simp only [c, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Units.val_mk0, map_pow,
      map_inv₀, h2, one_div, inv_pow]
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  refine ⟨C, i * nn F * Real.log 2, hC, by positivity, fun h => ?_⟩
  by_cases hne : (boxS Sf h).Nonempty
  · obtain ⟨ξ₀, hξ₀⟩ := hne
    have hh1 := norm_le_one_of_box h ξ₀ hξ₀
    have hpos := sIdeleNorm_pos Sf h
    have hsub : boxS Sf h ⊆ boxS Sf (mkId c 1 * h) := by
      rintro ξ ⟨hS, hinf, hfin⟩
      refine ⟨hS, fun w => ?_, fun v => ?_⟩
      · have e1 : ‖(sDiagonal Sf (ξ : F) *
            ((mkId c 1 * h : SIdeleGroup F Sf) : SAdeleRing F Sf)).1 w‖ =
            w (c : F) * ‖(sDiagonal Sf (ξ : F) * (h : SAdeleRing F Sf)).1 w‖ := by
          simp only [norm_diag_inf, mkId_fst]
          ring
        rw [e1, hwc]
        have h3 := hinf w
        have h0 : (1 / 2 : ℝ) ^ i ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
        have h4 := norm_nonneg ((sDiagonal Sf (ξ : F) * (h : SAdeleRing F Sf)).1 w)
        have h5 : (0 : ℝ) ≤ (1 / 2) ^ i := by positivity
        nlinarith
      · have e2 : (sDiagonal Sf (ξ : F) *
            ((mkId c 1 * h : SIdeleGroup F Sf) : SAdeleRing F Sf)).2 v =
            (sDiagonal Sf (ξ : F) * (h : SAdeleRing F Sf)).2 v := by
          show (sDiagonal Sf (ξ : F)).2 v * ((sDiagonal Sf ((1 : Fˣ) : F)).2 v *
            (h : SAdeleRing F Sf).2 v) = (sDiagonal Sf (ξ : F)).2 v * (h : SAdeleRing F Sf).2 v
          rw [Units.val_one, map_one, Prod.snd_one, Pi.one_apply, one_mul]
        rw [e2]
        exact hfin v
    have hnorm : sIdeleNorm Sf (mkId c 1 * h) = (1 / 2 : ℝ) ^ (i * nn F) * sIdeleNorm Sf h := by
      rw [norm_mkId]
      simp only [hwc, Units.val_one, fin_coe_one', norm_one, Finset.prod_const_one, mul_one]
      rw [Finset.prod_pow_eq_pow_sum, ← pow_mul]
      rfl
    have hh' : sIdeleNorm Sf (mkId c 1 * h) < ε := by
      rw [hnorm]
      have h1 : (1 / 2 : ℝ) ^ (i * nn F) ≤ (1 / 2) ^ i :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_mul_of_pos_right i one_le_nn)
      have h2 : (0 : ℝ) ≤ (1 / 2) ^ (i * nn F) := by positivity
      have h3 : (1 / 2 : ℝ) ^ (i * nn F) * sIdeleNorm Sf h ≤ (1 / 2) ^ (i * nn F) := by
        nlinarith
      linarith
    obtain ⟨hfin', hcard'⟩ := hcount (mkId c 1 * h) hh'
    have hfinS : (boxS Sf (mkId c 1 * h)).Finite := hfin'
    have hcardS : ((boxS Sf (mkId c 1 * h)).ncard : ℝ) ≤
        C * |Real.log (sIdeleNorm Sf (mkId c 1 * h))| ^ rk F Sf := hcard'
    refine ⟨hfinS.subset hsub, ?_⟩
    have hle : ((boxS Sf h).ncard : ℝ) ≤ (boxS Sf (mkId c 1 * h)).ncard := by
      exact_mod_cast Set.ncard_le_ncard hsub hfinS
    have hlog : |Real.log (sIdeleNorm Sf (mkId c 1 * h))| =
        |Real.log (sIdeleNorm Sf h)| + i * nn F * Real.log 2 := by
      rw [hnorm, Real.log_mul (by positivity) hpos.ne', Real.log_pow, one_div, Real.log_inv]
      have hl1 : Real.log (sIdeleNorm Sf h) ≤ 0 := Real.log_nonpos hpos.le hh1
      have hm : (0 : ℝ) ≤ ((i * nn F : ℕ) : ℝ) * Real.log 2 := by positivity
      rw [abs_of_nonpos (by linarith), abs_of_nonpos hl1]
      push_cast
      ring
    rw [hlog] at hcardS
    linarith
  · have hempty : boxS Sf h = ∅ := Set.not_nonempty_iff_eq_empty.1 hne
    rw [hempty, Set.ncard_empty, Nat.cast_zero]
    exact ⟨Set.finite_empty, by positivity⟩

lemma exists_fin_scalar (R : ℝ) : ∃ d : Fˣ, ∀ v : Sf,
    ‖((d : F) : (v : HeightOneSpectrum (𝓞 F)).adicCompletion F)‖ * R ≤ 1 := by
  classical
  let a : 𝓞 F := ∏ v ∈ Sf, (Ideal.absNorm v.asIdeal : 𝓞 F)
  have ha0 : a ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun v _ => ?_
    have := NumberField.HeightOneSpectrum.one_lt_absNorm v
    exact_mod_cast (show Ideal.absNorm v.asIdeal ≠ 0 by omega)
  have ha0' : (a : F) ≠ 0 := NumberField.RingOfIntegers.coe_ne_zero_iff.2 ha0
  have hmem : ∀ v ∈ Sf, a ∈ v.asIdeal := fun v hv => by
    obtain ⟨b, hb⟩ := Finset.dvd_prod_of_mem (fun v => (Ideal.absNorm v.asIdeal : 𝓞 F)) hv
    have : a = (Ideal.absNorm v.asIdeal : 𝓞 F) * b := hb
    rw [this]
    exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)
  have hq : ∀ v : Sf, ‖((a : F) : (v : HeightOneSpectrum (𝓞 F)).adicCompletion F)‖ < 1 :=
    fun v => (FinitePlace.norm_lt_one_iff_mem (K := F) (v : HeightOneSpectrum (𝓞 F)) a).2
      (hmem v v.2)
  let R' := max R 1
  have hR' : 0 < R' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hk : ∀ v : Sf, ∃ k : ℕ,
      ‖((a : F) : (v : HeightOneSpectrum (𝓞 F)).adicCompletion F)‖ ^ k < 1 / R' :=
    fun v => exists_pow_lt_of_lt_one (by positivity) (hq v)
  let k : Sf → ℕ := fun v => (hk v).choose
  let K := ∑ v, k v
  refine ⟨Units.mk0 ((a : F) ^ K) (pow_ne_zero _ ha0'), fun v => ?_⟩
  show ‖FinitePlace.embedding (v : HeightOneSpectrum (𝓞 F)) ((a : F) ^ K)‖ * R ≤ 1
  rw [map_pow, norm_pow]
  have hq0 : 0 ≤ ‖FinitePlace.embedding (v : HeightOneSpectrum (𝓞 F)) (a : F)‖ := norm_nonneg _
  have hq1 : ‖FinitePlace.embedding (v : HeightOneSpectrum (𝓞 F)) (a : F)‖ < 1 := hq v
  have hkv : k v ≤ K := Finset.single_le_sum (f := k) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ v)
  have h1 : ‖FinitePlace.embedding (v : HeightOneSpectrum (𝓞 F)) (a : F)‖ ^ K ≤
      ‖FinitePlace.embedding (v : HeightOneSpectrum (𝓞 F)) (a : F)‖ ^ k v :=
    pow_le_pow_of_le_one hq0 hq1.le hkv
  have h2 : ‖FinitePlace.embedding (v : HeightOneSpectrum (𝓞 F)) (a : F)‖ ^ k v < 1 / R' :=
    (hk v).choose_spec
  have h3 : 0 ≤ ‖FinitePlace.embedding (v : HeightOneSpectrum (𝓞 F)) (a : F)‖ ^ K := by
    positivity
  have h4 : ‖FinitePlace.embedding (v : HeightOneSpectrum (𝓞 F)) (a : F)‖ ^ K * R ≤
      ‖FinitePlace.embedding (v : HeightOneSpectrum (𝓞 F)) (a : F)‖ ^ K * R' :=
    mul_le_mul_of_nonneg_left (le_max_left _ _) h3
  have h5 : ‖FinitePlace.embedding (v : HeightOneSpectrum (𝓞 F)) (a : F)‖ ^ K * R' <
      1 / R' * R' := mul_lt_mul_of_pos_right (lt_of_le_of_lt h1 h2) hR'
  rw [div_mul_cancel₀ (1 : ℝ) hR'.ne'] at h5
  linarith

/-- the shells -/
def shellS (Sf : Finset (HeightOneSpectrum (𝓞 F))) (R : ℝ) (g : SIdeleGroup F Sf) (j : ℕ) :
    Set Fˣ :=
  {ξ : Fˣ | ξ ∈ SUnits Sf ∧
    (∀ w : InfinitePlace F, ‖(sDiagonal Sf (ξ : F) * (g : SAdeleRing F Sf)).1 w‖ ≤ (j : ℝ) + 1) ∧
    ∀ v : Sf, ‖(sDiagonal Sf (ξ : F) * (g : SAdeleRing F Sf)).2 v‖ ≤ R}

lemma shell_count (R : ℝ) : ∃ C K₁ : ℝ, 0 < C ∧ 0 ≤ K₁ ∧ ∀ (g : SIdeleGroup F Sf) (j : ℕ),
    (shellS Sf R g j).Finite ∧ ((shellS Sf R g j).ncard : ℝ) ≤
      C * (|Real.log (sIdeleNorm Sf g)| + nn F * j + K₁) ^ rk F Sf := by
  obtain ⟨C, K₀, hC, hK₀, hcount⟩ := count_all (F := F) (Sf := Sf)
  obtain ⟨d, hd⟩ := exists_fin_scalar (Sf := Sf) R
  let κ : ℝ := ∏ v : Sf, ‖((d : F) : (v : HeightOneSpectrum (𝓞 F)).adicCompletion F)‖
  have hκ : 0 < κ := Finset.prod_pos fun v _ => norm_pos_iff.2 (fin_coe_ne_zero _ d.ne_zero)
  refine ⟨C, |Real.log κ| + K₀, hC, by positivity, fun g j => ?_⟩
  have hj0 : ((j : F) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
  let c : Fˣ := (Units.mk0 ((j : F) + 1) hj0)⁻¹
  have hwc : ∀ w : InfinitePlace F, w (c : F) = ((j : ℝ) + 1)⁻¹ := by
    intro w
    have h2 : w ((j : F) + 1) = (j : ℝ) + 1 := by
      have := InfinitePlace.map_natCast w (j + 1)
      exact_mod_cast this
    simp only [c, Units.val_inv_eq_inv_val, Units.val_mk0, map_inv₀, h2]
  have hj1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hsub : shellS Sf R g j ⊆ boxS Sf (mkId c d * g) := by
    rintro ξ ⟨hS, hinf, hfin⟩
    refine ⟨hS, fun w => ?_, fun v => ?_⟩
    · have e1 : ‖(sDiagonal Sf (ξ : F) *
          ((mkId c d * g : SIdeleGroup F Sf) : SAdeleRing F Sf)).1 w‖ =
          w (c : F) * ‖(sDiagonal Sf (ξ : F) * (g : SAdeleRing F Sf)).1 w‖ := by
        simp only [norm_diag_inf, mkId_fst]
        ring
      rw [e1, hwc, inv_mul_le_iff₀ hj1, mul_one]
      exact hinf w
    · have e2 : (sDiagonal Sf (ξ : F) *
          ((mkId c d * g : SIdeleGroup F Sf) : SAdeleRing F Sf)).2 v =
          (sDiagonal Sf (d : F) * (sDiagonal Sf (ξ : F) * (g : SAdeleRing F Sf))).2 v := by
        show (sDiagonal Sf (ξ : F)).2 v * ((sDiagonal Sf (d : F)).2 v *
          (g : SAdeleRing F Sf).2 v) = (sDiagonal Sf (d : F)).2 v *
            ((sDiagonal Sf (ξ : F)).2 v * (g : SAdeleRing F Sf).2 v)
        ring
      have hn : ‖(sDiagonal Sf (ξ : F) *
          ((mkId c d * g : SIdeleGroup F Sf) : SAdeleRing F Sf)).2 v‖ ≤ 1 := by
        rw [e2, norm_diag_fin]
        have h1 := hfin v
        have h2 := hd v
        have h3 := norm_nonneg ((d : F) : (v : HeightOneSpectrum (𝓞 F)).adicCompletion F)
        nlinarith
      exact Valued.toNormedField.norm_le_one_iff.mp hn
  obtain ⟨hfin', hcard'⟩ := hcount (mkId c d * g)
  refine ⟨hfin'.subset hsub, ?_⟩
  have hle : ((shellS Sf R g j).ncard : ℝ) ≤ (boxS Sf (mkId c d * g)).ncard := by
    exact_mod_cast Set.ncard_le_ncard hsub hfin'
  have hgpos := sIdeleNorm_pos Sf g
  have hnorm : sIdeleNorm Sf (mkId c d * g) = ((j : ℝ) + 1)⁻¹ ^ nn F * κ * sIdeleNorm Sf g := by
    rw [norm_mkId]
    simp only [hwc]
    rw [Finset.prod_pow_eq_pow_sum]
    rfl
  have hlog : |Real.log (sIdeleNorm Sf (mkId c d * g))| ≤
      |Real.log (sIdeleNorm Sf g)| + nn F * j + |Real.log κ| := by
    rw [hnorm, Real.log_mul (by positivity) hgpos.ne', Real.log_mul (by positivity) hκ.ne',
      Real.log_pow, Real.log_inv]
    have hl : Real.log ((j : ℝ) + 1) ≤ j := by
      have := Real.log_le_sub_one_of_pos hj1
      linarith
    have hl0 : 0 ≤ Real.log ((j : ℝ) + 1) := Real.log_nonneg (by linarith)
    have hn0 : (0 : ℝ) ≤ nn F := Nat.cast_nonneg _
    have h1 : |(nn F : ℝ) * -Real.log ((j : ℝ) + 1)| ≤ nn F * j := by
      rw [abs_mul, abs_neg, abs_of_nonneg hl0, abs_of_nonneg hn0]
      exact mul_le_mul_of_nonneg_left hl hn0
    calc |(nn F : ℝ) * -Real.log ((j : ℝ) + 1) + Real.log κ + Real.log (sIdeleNorm Sf g)|
        ≤ |(nn F : ℝ) * -Real.log ((j : ℝ) + 1) + Real.log κ| + |Real.log (sIdeleNorm Sf g)| :=
          abs_add_le _ _
      _ ≤ |(nn F : ℝ) * -Real.log ((j : ℝ) + 1)| + |Real.log κ| +
          |Real.log (sIdeleNorm Sf g)| := by
          have := abs_add_le ((nn F : ℝ) * -Real.log ((j : ℝ) + 1)) (Real.log κ)
          linarith
      _ ≤ |Real.log (sIdeleNorm Sf g)| + nn F * j + |Real.log κ| := by linarith
  have hpow : (|Real.log (sIdeleNorm Sf (mkId c d * g))| + K₀) ^ rk F Sf ≤
      (|Real.log (sIdeleNorm Sf g)| + nn F * j + (|Real.log κ| + K₀)) ^ rk F Sf :=
    pow_le_pow_left₀ (by positivity) (by linarith) _
  have := mul_le_mul_of_nonneg_left hpow hC.le
  linarith

end Count

section Theta

variable {F : Type*} [Field F] [NumberField F] {Sf : Finset (HeightOneSpectrum (𝓞 F))}

lemma sum_inv_sq_le (J : ℕ) : ∑ j ∈ Finset.range J, 1 / (1 + (j : ℝ)) ^ 2 ≤ 2 := by
  have key : ∀ J : ℕ, ∑ j ∈ Finset.range (J + 1), 1 / (1 + (j : ℝ)) ^ 2 ≤
      2 - 1 / (1 + (J : ℝ)) := by
    intro J
    induction J with
    | zero => norm_num
    | succ J ih =>
      rw [Finset.sum_range_succ]
      have hJ : (0 : ℝ) < 1 + (J : ℝ) := by positivity
      have hJ2 : (0 : ℝ) < 1 + ((J + 1 : ℕ) : ℝ) := by positivity
      have h1 : 1 / (1 + ((J + 1 : ℕ) : ℝ)) ^ 2 ≤
          1 / (1 + (J : ℝ)) - 1 / (1 + ((J + 1 : ℕ) : ℝ)) := by
        rw [div_sub_div _ _ hJ.ne' hJ2.ne', div_le_div_iff₀ (by positivity) (by positivity)]
        push_cast
        nlinarith
      linarith
  have h1 := key J
  have h2 : ∑ j ∈ Finset.range J, 1 / (1 + (j : ℝ)) ^ 2 ≤
      ∑ j ∈ Finset.range (J + 1), 1 / (1 + (j : ℝ)) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (Nat.le_succ J))
      (fun _ _ _ => by positivity)
  have h3 : 0 ≤ 1 / (1 + (J : ℝ)) := by positivity
  linarith

lemma term_le (C₀ C L K₁ n : ℝ) (j r : ℕ) (hC₀ : 0 ≤ C₀) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hK : 0 ≤ K₁) (hn : 0 ≤ n) :
    C₀ / (1 + (j : ℝ)) ^ (r + 2) * (C * (L + n * j + K₁) ^ r) ≤
      C₀ * C * (L + (K₁ + n)) ^ r * (1 / (1 + (j : ℝ)) ^ 2) := by
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hj : (0 : ℝ) < 1 + j := by positivity
  have h1 : L + n * j + K₁ ≤ (L + (K₁ + n)) * (1 + j) := by
    have e : (L + (K₁ + n)) * (1 + j) = L + n * j + K₁ + (n + L * j + K₁ * j) := by ring
    rw [e]
    have : 0 ≤ n + L * j + K₁ * j := by positivity
    linarith
  have h2 : (L + n * j + K₁) ^ r ≤ (L + (K₁ + n)) ^ r * (1 + j) ^ r := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h1 r
  have h3 : C₀ / (1 + (j : ℝ)) ^ (r + 2) * (C * (L + n * j + K₁) ^ r) ≤
      C₀ / (1 + (j : ℝ)) ^ (r + 2) * (C * ((L + (K₁ + n)) ^ r * (1 + j) ^ r)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hC) (by positivity)
  have h4 : C₀ / (1 + (j : ℝ)) ^ (r + 2) * (C * ((L + (K₁ + n)) ^ r * (1 + j) ^ r)) =
      C₀ * C * (L + (K₁ + n)) ^ r * (1 / (1 + (j : ℝ)) ^ 2) := by
    have hne : (1 + (j : ℝ)) ^ r ≠ 0 := by positivity
    have hne2 : (1 + (j : ℝ)) ^ 2 ≠ 0 := by positivity
    rw [pow_add]
    field_simp
  linarith

lemma theta_bound (R : ℝ) : ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ (ψ : SAdeleRing F Sf → ℝ) (C₀ : ℝ),
    (∀ x, 0 ≤ ψ x) → (∀ x, ψ x ≠ 0 → ∀ v : Sf, ‖x.2 v‖ ≤ R) →
    (∀ x, (1 + infN x.1) ^ (rk F Sf + 2) * ψ x ≤ C₀) →
    ∀ (g : SIdeleGroup F Sf) (s : Finset (SUnits Sf)),
      ∑ ξ ∈ s, ψ (sDiagonal Sf ((ξ : Fˣ) : F) * (g : SAdeleRing F Sf)) ≤
        C₀ * A * (|Real.log (sIdeleNorm Sf g)| + B) ^ rk F Sf := by
  classical
  obtain ⟨C, K₁, hC, hK₁, hsh⟩ := shell_count (Sf := Sf) R
  refine ⟨2 * C, K₁ + nn F, by positivity, by positivity, fun ψ C₀ hψ0 hsupp hdec g s => ?_⟩
  have hC₀ : 0 ≤ C₀ := by
    have h1 := hdec 0
    have h2 : 0 ≤ (1 + infN (0 : SAdeleRing F Sf).1) ^ (rk F Sf + 2) * ψ 0 :=
      mul_nonneg (pow_nonneg (by linarith [infN_nonneg (0 : SAdeleRing F Sf).1]) _) (hψ0 0)
    linarith
  obtain ⟨L, hL⟩ : ∃ L, L = |Real.log (sIdeleNorm Sf g)| := ⟨_, rfl⟩
  rw [← hL]
  have hL0 : 0 ≤ L := by rw [hL]; exact abs_nonneg _
  let X : SUnits Sf → SAdeleRing F Sf := fun ξ => sDiagonal Sf ((ξ : Fˣ) : F) * (g : SAdeleRing F Sf)
  let jj : SUnits Sf → ℕ := fun ξ => ⌊infN (X ξ).1⌋₊
  let J := s.sup jj + 1
  let a : ℕ → ℝ := fun j => C₀ / (1 + (j : ℝ)) ^ (rk F Sf + 2)
  have ha0 : ∀ j, 0 ≤ a j := fun j => div_nonneg hC₀ (by positivity)
  have hind : ∀ (j : ℕ) (ξ : SUnits Sf),
      (0 : ℝ) ≤ (if ((ξ : Fˣ) ∈ shellS Sf R g j) then 1 else 0) := by
    intro j ξ
    split_ifs <;> norm_num
  have hpt : ∀ ξ ∈ s, ψ (X ξ) ≤ ∑ j ∈ Finset.range J,
      a j * (if ((ξ : Fˣ) ∈ shellS Sf R g j) then 1 else 0) := by
    intro ξ hξ
    by_cases h0 : ψ (X ξ) = 0
    · rw [h0]
      exact Finset.sum_nonneg fun j _ => mul_nonneg (ha0 j) (hind j ξ)
    · have hj : jj ξ ∈ Finset.range J :=
        Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.le_sup (f := jj) hξ))
      have hmem : (ξ : Fˣ) ∈ shellS Sf R g (jj ξ) := by
        refine ⟨ξ.2, fun w => ?_, fun v => hsupp _ h0 v⟩
        exact (norm_le_infN _ w).trans (Nat.lt_floor_add_one _).le
      have hterm : ψ (X ξ) ≤ a (jj ξ) * (if ((ξ : Fˣ) ∈ shellS Sf R g (jj ξ)) then 1 else 0) := by
        rw [if_pos hmem, mul_one]
        have hI := infN_nonneg (X ξ).1
        have hpos : 0 < (1 + infN (X ξ).1) ^ (rk F Sf + 2) := pow_pos (by linarith) _
        have h1 : ψ (X ξ) ≤ C₀ / (1 + infN (X ξ).1) ^ (rk F Sf + 2) := by
          rw [le_div_iff₀ hpos, mul_comm]
          exact hdec _
        have h2 : (1 + (jj ξ : ℝ)) ^ (rk F Sf + 2) ≤ (1 + infN (X ξ).1) ^ (rk F Sf + 2) :=
          pow_le_pow_left₀ (by positivity) (by linarith [Nat.floor_le hI]) _
        exact h1.trans (div_le_div_of_nonneg_left hC₀ (by positivity) h2)
      refine hterm.trans ?_
      exact Finset.single_le_sum
        (f := fun j => a j * (if ((ξ : Fˣ) ∈ shellS Sf R g j) then (1 : ℝ) else 0))
        (fun j _ => mul_nonneg (ha0 j) (hind j ξ)) hj
  have hswap : ∑ ξ ∈ s, ∑ j ∈ Finset.range J,
      a j * (if ((ξ : Fˣ) ∈ shellS Sf R g j) then (1 : ℝ) else 0) =
      ∑ j ∈ Finset.range J, a j * ((s.filter (fun ξ : SUnits Sf =>
        (ξ : Fˣ) ∈ shellS Sf R g j)).card : ℝ) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.mul_sum, Finset.sum_boole]
  have hcard : ∀ j, ((s.filter (fun ξ : SUnits Sf => (ξ : Fˣ) ∈ shellS Sf R g j)).card : ℝ) ≤
      C * (L + nn F * j + K₁) ^ rk F Sf := by
    intro j
    obtain ⟨hfin, hc⟩ := hsh g j
    rw [← hL] at hc
    have h1 : (s.filter (fun ξ : SUnits Sf => (ξ : Fˣ) ∈ shellS Sf R g j)).card ≤
        (shellS Sf R g j).ncard := by
      rw [← Finset.card_map (Function.Embedding.subtype (fun x : Fˣ => x ∈ SUnits Sf)),
        ← Set.ncard_coe_finset]
      apply Set.ncard_le_ncard _ hfin
      intro x hx
      rw [Finset.coe_map, Set.mem_image] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact (Finset.mem_filter.1 hy).2
    have h2 : ((s.filter (fun ξ : SUnits Sf => (ξ : Fˣ) ∈ shellS Sf R g j)).card : ℝ) ≤
        (shellS Sf R g j).ncard := by exact_mod_cast h1
    exact h2.trans hc
  have hn0 : (0 : ℝ) ≤ nn F := Nat.cast_nonneg _
  calc ∑ ξ ∈ s, ψ (sDiagonal Sf ((ξ : Fˣ) : F) * (g : SAdeleRing F Sf))
      = ∑ ξ ∈ s, ψ (X ξ) := rfl
    _ ≤ ∑ ξ ∈ s, ∑ j ∈ Finset.range J,
        a j * (if ((ξ : Fˣ) ∈ shellS Sf R g j) then (1 : ℝ) else 0) := Finset.sum_le_sum hpt
    _ = ∑ j ∈ Finset.range J, a j * ((s.filter (fun ξ : SUnits Sf =>
        (ξ : Fˣ) ∈ shellS Sf R g j)).card : ℝ) := hswap
    _ ≤ ∑ j ∈ Finset.range J, a j * (C * (L + nn F * j + K₁) ^ rk F Sf) :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hcard j) (ha0 j)
    _ ≤ ∑ j ∈ Finset.range J, C₀ * C * (L + (K₁ + nn F)) ^ rk F Sf * (1 / (1 + (j : ℝ)) ^ 2) :=
        Finset.sum_le_sum fun j _ => term_le C₀ C L K₁ (nn F) j (rk F Sf) hC₀ hC.le hL0 hK₁ hn0
    _ = C₀ * C * (L + (K₁ + nn F)) ^ rk F Sf *
        ∑ j ∈ Finset.range J, 1 / (1 + (j : ℝ)) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ C₀ * C * (L + (K₁ + nn F)) ^ rk F Sf * 2 :=
        mul_le_mul_of_nonneg_left (sum_inv_sq_le J) (by positivity)
    _ = C₀ * (2 * C) * (L + (K₁ + nn F)) ^ rk F Sf := by ring

/-- summability and the bound for a single dominated function -/
lemma theta_main (R : ℝ) : ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ (f : SAdelicSchwartz F Sf) (C₀ : ℝ),
    (∀ x, f.eval x ≠ 0 → ∀ v : Sf, ‖x.2 v‖ ≤ R) →
    (∀ x, (1 + infN x.1) ^ (rk F Sf + 2) * ‖f.eval x‖ ≤ C₀) →
    ∀ g : SIdeleGroup F Sf,
      Summable (fun ξ : SUnits Sf =>
        ‖f.eval (sDiagonal Sf ((ξ : Fˣ) : F) * (g : SAdeleRing F Sf))‖) ∧
      ‖sLocalTheta f g‖ ≤ C₀ * A * (|Real.log (sIdeleNorm Sf g)| + B) ^ rk F Sf := by
  obtain ⟨A, B, hA, hB, hb⟩ := theta_bound (Sf := Sf) R
  refine ⟨A, B, hA, hB, fun f C₀ hsupp hdec g => ?_⟩
  have hb' := hb (fun x => ‖f.eval x‖) C₀ (fun x => norm_nonneg _)
    (fun x hx => hsupp x (fun h => hx (by rw [h, norm_zero]))) hdec g
  have hs : Summable (fun ξ : SUnits Sf =>
      ‖f.eval (sDiagonal Sf ((ξ : Fˣ) : F) * (g : SAdeleRing F Sf))‖) :=
    summable_of_sum_le (fun _ => norm_nonneg _) hb'
  refine ⟨hs, ?_⟩
  unfold sLocalTheta
  exact (norm_tsum_le_tsum_norm hs).trans (Real.tsum_le_of_sum_le (fun _ => norm_nonneg _) hb')

end Theta

section Asym

lemma rpow_log_bound (B : ℝ) (hB : 0 ≤ B) (r : ℕ) (η : ℝ) (hη : 0 < η) (y : ℝ) (hy : 0 < y)
    (hy1 : y < 1) :
    y ^ η * (|Real.log y| + B) ^ r ≤ (r.factorial : ℝ) / η ^ r * Real.exp (η * B) := by
  have hl : Real.log y < 0 := Real.log_neg hy hy1
  obtain ⟨t, ht⟩ : ∃ t, t = -Real.log y := ⟨_, rfl⟩
  have ht0 : 0 ≤ t := by linarith
  have habs : |Real.log y| = t := by rw [abs_of_neg hl, ht]
  have hyη : y ^ η = Real.exp (-(η * t)) := by
    rw [Real.rpow_def_of_pos hy, ht]
    congr 1
    ring
  rw [hyη, habs]
  have hηr : 0 < η ^ r := pow_pos hη r
  have hfac : (0 : ℝ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
  have h1 := Real.pow_div_factorial_le_exp (η * (t + B)) (by positivity) r
  rw [div_le_iff₀ hfac] at h1
  have h2 : (t + B) ^ r * η ^ r = (η * (t + B)) ^ r := by rw [mul_pow]; ring
  have h3 : Real.exp (-(η * t)) * Real.exp (η * (t + B)) = Real.exp (η * B) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [div_mul_eq_mul_div, le_div_iff₀ hηr]
  have hE : 0 ≤ Real.exp (-(η * t)) := (Real.exp_pos _).le
  calc Real.exp (-(η * t)) * (t + B) ^ r * η ^ r = Real.exp (-(η * t)) * (η * (t + B)) ^ r := by
        rw [mul_assoc, h2]
    _ ≤ Real.exp (-(η * t)) * (Real.exp (η * (t + B)) * (r.factorial : ℝ)) :=
        mul_le_mul_of_nonneg_left h1 hE
    _ = (r.factorial : ℝ) * Real.exp (η * B) := by rw [← h3]; ring

variable {F : Type*} [Field F] [NumberField F] {Sf : Finset (HeightOneSpectrum (𝓞 F))}

/-- per-`f` bound on the `S`-local theta function -/
lemma theta_single (f : SAdelicSchwartz F Sf) : ∃ K B : ℝ, 0 ≤ K ∧ 0 ≤ B ∧
    ∀ g : SIdeleGroup F Sf,
      ‖sLocalTheta f g‖ ≤ K * (|Real.log (sIdeleNorm Sf g)| + B) ^ rk F Sf := by
  obtain ⟨⟨R, hR⟩, hD, -⟩ := eval_good f
  obtain ⟨C₀, hC₀⟩ := hD (rk F Sf + 2)
  obtain ⟨A, B, hA, hB, hmain⟩ := theta_main (Sf := Sf) R
  refine ⟨|C₀ * A|, B, abs_nonneg _, hB, fun g => ?_⟩
  have h1 := (hmain f C₀ hR hC₀ g).2
  have h2 : C₀ * A * (|Real.log (sIdeleNorm Sf g)| + B) ^ rk F Sf ≤
      |C₀ * A| * (|Real.log (sIdeleNorm Sf g)| + B) ^ rk F Sf :=
    mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
  linarith

end Asym

section Bounded

universe u

lemma cont_of_seminorm {X : Type*} [TopologicalSpace X] {E : Type u} [AddCommGroup E]
    [Module ℂ E] (p : Seminorm ℂ E) (φ : X → E)
    (hφ : ∀ (x₀ : X) (ε : ℝ), 0 < ε → ∀ᶠ x in 𝓝 x₀, p (φ x - φ x₀) < ε) :
    @Continuous X E _ (SeminormFamily.moduleFilterBasis (fun _ : PUnit.{u + 1} => p)).topology
      φ := by
  letI : TopologicalSpace E :=
    (SeminormFamily.moduleFilterBasis (fun _ : PUnit.{u + 1} => p)).topology
  have hws : WithSeminorms (fun _ : PUnit.{u + 1} => p) := ⟨rfl⟩
  rw [continuous_iff_continuousAt]
  intro x₀
  exact (hws.tendsto_nhds φ (φ x₀)).2 fun _ ε hε => hφ x₀ ε hε

lemma bdd_of_seminorm {E : Type u} [AddCommGroup E] [Module ℂ E] (p : Seminorm ℂ E) (B : Set E)
    (hB : @Bornology.IsVonNBounded ℂ E _ _ _
      (SeminormFamily.moduleFilterBasis (fun _ : PUnit.{u + 1} => p)).topology B) :
    ∃ r : ℝ, ∀ f ∈ B, p f < r := by
  letI : TopologicalSpace E :=
    (SeminormFamily.moduleFilterBasis (fun _ : PUnit.{u + 1} => p)).topology
  have hws : WithSeminorms (fun _ : PUnit.{u + 1} => p) := ⟨rfl⟩
  obtain ⟨r, -, hr⟩ := (hws.isVonNBounded_iff_seminorm_bounded).1 hB PUnit.unit
  exact ⟨r, hr⟩

lemma lc_of_seminorm {E : Type u} [AddCommGroup E] [Module ℂ E] (p : Seminorm ℂ E) :
    IsLocallyConvexTopology E
      (SeminormFamily.moduleFilterBasis (fun _ : PUnit.{u + 1} => p)).topology := by
  letI : TopologicalSpace E :=
    (SeminormFamily.moduleFilterBasis (fun _ : PUnit.{u + 1} => p)).topology
  exact ⟨PUnit.{u + 1}, inferInstance, fun _ => p, ⟨rfl⟩⟩

variable {m n r s : ℕ} {d : Fin s → ℕ}

lemma elem_nhds (g₀ : ElemSchwartz m n r s d) (i j : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ g in 𝓝 g₀, ∀ e : ElemGroup m n r s d,
      ‖e.2.2.1‖ ^ j * ‖e.1‖ ^ i * ‖(g - g₀).toFun e‖ < δ := by
  have h1 : Continuous (fun (g : ElemSchwartz m n r s d) (p : ℕ × ℕ × ℕ) =>
      UniformFun.ofFun
        (fun q : (Fin r → ℤ) × ((i : Fin s) → ZMod (d i)) × ((Fin m → ℝ) × (Fin n → ℝ)) =>
          (‖q.1‖ ^ p.2.1 * ‖q.2.2.1‖ ^ p.1) •
            iteratedFDeriv ℝ p.2.2 (elemLift g.toFun q.1 q.2.1) q.2.2)) :=
    continuous_induced_dom
  have h2 := ((continuous_apply ((i, j, 0) : ℕ × ℕ × ℕ)).comp h1).tendsto g₀
  rw [UniformFun.tendsto_iff_tendstoUniformly] at h2
  have h4 := Metric.tendstoUniformly_iff.1 h2 δ hδ
  filter_upwards [h4] with g hg
  intro e
  obtain ⟨t, ht⟩ := lift_circle e.2.1
  have h5 := hg (e.2.2.1, e.2.2.2, (e.1, t))
  simp only [Function.comp_apply, UniformFun.toFun_ofFun, iteratedFDeriv_zero_eq_comp] at h5
  rw [dist_eq_norm, ← smul_sub, norm_smul, ← map_sub, LinearIsometryEquiv.norm_map,
    elemLift_eq _ e t ht, elemLift_eq _ e t ht, Real.norm_of_nonneg (by positivity)] at h5
  have h6 : (g - g₀).toFun e = g.toFun e - g₀.toFun e := rfl
  rw [h6, norm_sub_rev]
  exact h5

end Bounded

section Weight

universe u

variable {F : Type u} [Field F] [NumberField F] {Sf : Finset (HeightOneSpectrum (𝓞 F))}

/-- admissible weights: polynomially bounded on each set of bounded finite components -/
def Adm (w : SAdeleRing F Sf → ℝ) : Prop :=
  (∀ x, 0 ≤ w x) ∧ ∀ L : ℝ, ∃ K : ℝ, ∃ N : ℕ, 0 ≤ K ∧
    ∀ x : SAdeleRing F Sf, (∀ v : Sf, ‖x.2 v‖ ≤ L) → w x ≤ K * (1 + infN x.1) ^ N

lemma adm_bdd (w : SAdeleRing F Sf → ℝ) (hw : Adm w) (f : SAdelicSchwartz F Sf) :
    BddAbove (Set.range fun x => w x * ‖f.eval x‖) := by
  obtain ⟨⟨R, hR⟩, hD, -⟩ := eval_good f
  obtain ⟨K, N, hK, hKw⟩ := hw.2 R
  obtain ⟨C, hC⟩ := hD N
  refine ⟨max (K * C) 0, ?_⟩
  rintro _ ⟨x, rfl⟩
  show w x * ‖f.eval x‖ ≤ max (K * C) 0
  by_cases h0 : f.eval x = 0
  · rw [h0, norm_zero, mul_zero]
    exact le_max_right _ _
  · have h1 := hKw x (hR x h0)
    have h2 : w x * ‖f.eval x‖ ≤ K * (1 + infN x.1) ^ N * ‖f.eval x‖ :=
      mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    have h3 : K * (1 + infN x.1) ^ N * ‖f.eval x‖ ≤ K * C := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (hC x) hK
    exact (h2.trans h3).trans (le_max_left _ _)

lemma eval_add (f g : SAdelicSchwartz F Sf) (x : SAdeleRing F Sf) :
    (f + g).eval x = f.eval x + g.eval x := rfl

lemma eval_smul (c : ℂ) (f : SAdelicSchwartz F Sf) (x : SAdeleRing F Sf) :
    (c • f).eval x = c * f.eval x := rfl

/-- the weighted sup seminorm -/
noncomputable def pw (w : SAdeleRing F Sf → ℝ) (hw : Adm w) : Seminorm ℂ (SAdelicSchwartz F Sf) :=
  Seminorm.of (fun f => ⨆ x, w x * ‖f.eval x‖)
    (by
      intro f g
      refine ciSup_le fun x => ?_
      have h1 : w x * ‖(f + g).eval x‖ ≤ w x * ‖f.eval x‖ + w x * ‖g.eval x‖ := by
        rw [eval_add, ← mul_add]
        exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (hw.1 x)
      exact h1.trans (add_le_add (le_ciSup (adm_bdd w hw f) x) (le_ciSup (adm_bdd w hw g) x)))
    (by
      intro c f
      rw [Real.mul_iSup_of_nonneg (norm_nonneg c)]
      congr 1
      funext x
      rw [eval_smul, norm_mul]
      ring)

lemma le_pw (w : SAdeleRing F Sf → ℝ) (hw : Adm w) (f : SAdelicSchwartz F Sf)
    (x : SAdeleRing F Sf) : w x * ‖f.eval x‖ ≤ pw w hw f :=
  le_ciSup (adm_bdd w hw f) x

lemma pw_le (w : SAdeleRing F Sf → ℝ) (hw : Adm w) (f : SAdelicSchwartz F Sf) (M : ℝ)
    (hM : ∀ x, w x * ‖f.eval x‖ ≤ M) : pw w hw f ≤ M :=
  ciSup_le hM

lemma ofElem_sub {Γ k : Subgroup (Multiplicative (SAdeleRing F Sf))} {m n r s : ℕ}
    {d : Fin s → ℕ} (π : Γ →* Multiplicative (ElemGroup m n r s d))
    (hs : IsStructuralPair Γ k) (hπ : IsElemPresentation Γ k π) (g g₀ : ElemSchwartz m n r s d) :
    SchwartzBruhat.ofElem Γ k π hs hπ g - SchwartzBruhat.ofElem Γ k π hs hπ g₀ =
      SchwartzBruhat.ofElem Γ k π hs hπ (g - g₀) := by
  apply Subtype.ext
  funext x
  show extendPullback Γ π g.toFun x - extendPullback Γ π g₀.toFun x =
    extendPullback Γ π (g - g₀).toFun x
  by_cases hx : x ∈ Γ
  · rw [extendPullback_of_mem π _ x hx, extendPullback_of_mem π _ x hx,
      extendPullback_of_mem π _ x hx]
    rfl
  · rw [extendPullback_of_not_mem π _ x hx, extendPullback_of_not_mem π _ x hx,
      extendPullback_of_not_mem π _ x hx, sub_zero]

lemma ofElem_pw_cont (w : SAdeleRing F Sf → ℝ) (hw : Adm w)
    {Γ k : Subgroup (Multiplicative (SAdeleRing F Sf))} {m n r s : ℕ}
    {d : Fin s → ℕ} (π : Γ →* Multiplicative (ElemGroup m n r s d))
    (hs : IsStructuralPair Γ k) (hπ : IsElemPresentation Γ k π) :
    @Continuous (ElemSchwartz m n r s d) (SAdelicSchwartz F Sf) _
      (SeminormFamily.moduleFilterBasis (fun _ : PUnit.{u + 1} => pw w hw)).topology
      (SchwartzBruhat.ofElem Γ k π hs hπ) := by
  apply cont_of_seminorm
  intro g₀ ε hε
  obtain ⟨R, a, b, hR0, ha, hb, hR, hab⟩ := stage hs hπ
  obtain ⟨K, N, hK, hKw⟩ := hw.2 R
  let Q : ℝ := K * ((1 + a + b) ^ N * 4 ^ N * 4) + 1
  have hQ : 0 < Q := by positivity
  let δ : ℝ := ε / (2 * Q)
  have hδ : 0 < δ := by positivity
  filter_upwards [elem_nhds g₀ 0 0 δ hδ, elem_nhds g₀ N 0 δ hδ, elem_nhds g₀ 0 N δ hδ,
    elem_nhds g₀ N N δ hδ] with g h1 h2 h3 h4
  rw [ofElem_sub]
  have hbound : ∀ x : SAdeleRing F Sf,
      w x * ‖SAdelicSchwartz.eval (SchwartzBruhat.ofElem Γ k π hs hπ (g - g₀)) x‖ ≤
        K * ((1 + a + b) ^ N * 4 ^ N * (4 * δ)) := by
    intro x
    have hval : SAdelicSchwartz.eval (SchwartzBruhat.ofElem Γ k π hs hπ (g - g₀)) x =
        extendPullback Γ π (g - g₀).toFun (Multiplicative.ofAdd x) := rfl
    rw [hval]
    by_cases hx : Multiplicative.ofAdd x ∈ Γ
    · have hw1 := hKw x (fun v => hR _ hx v)
      have hgd := gen_decay (k := k) a b ha hb hab (g - g₀).toFun N δ hδ.le
        (fun e => ⟨(h1 e).le, (h2 e).le, (h3 e).le, (h4 e).le⟩) (Multiplicative.ofAdd x)
      have hx1 : infN (Multiplicative.toAdd (Multiplicative.ofAdd x)).1 = infN x.1 := rfl
      rw [hx1] at hgd
      calc w x * ‖extendPullback Γ π (g - g₀).toFun (Multiplicative.ofAdd x)‖
          ≤ K * (1 + infN x.1) ^ N *
            ‖extendPullback Γ π (g - g₀).toFun (Multiplicative.ofAdd x)‖ :=
            mul_le_mul_of_nonneg_right hw1 (norm_nonneg _)
        _ = K * ((1 + infN x.1) ^ N *
            ‖extendPullback Γ π (g - g₀).toFun (Multiplicative.ofAdd x)‖) := by ring
        _ ≤ K * ((1 + a + b) ^ N * 4 ^ N * (4 * δ)) := mul_le_mul_of_nonneg_left hgd hK
    · rw [extendPullback_of_not_mem π _ _ hx, norm_zero, mul_zero]
      positivity
  have h5 := pw_le w hw _ _ hbound
  have h6 : K * ((1 + a + b) ^ N * 4 ^ N * (4 * δ)) ≤ Q * δ := by
    have : K * ((1 + a + b) ^ N * 4 ^ N * (4 * δ)) = K * ((1 + a + b) ^ N * 4 ^ N * 4) * δ := by
      ring
    rw [this]
    exact mul_le_mul_of_nonneg_right (by linarith) hδ.le
  have h7 : Q * δ = ε / 2 := by
    show Q * (ε / (2 * Q)) = ε / 2
    field_simp
  linarith

lemma bdd_weight (w : SAdeleRing F Sf → ℝ) (hw : Adm w) (B : Set (SAdelicSchwartz F Sf))
    (hB : Bornology.IsVonNBounded ℂ B) :
    ∃ M : ℝ, ∀ f ∈ B, ∀ x, w x * ‖f.eval x‖ ≤ M := by
  let t := (SeminormFamily.moduleFilterBasis (fun _ : PUnit.{u + 1} => pw w hw)).topology
  have hmem : t ∈ {t | IsLocallyConvexTopology (SAdelicSchwartz F Sf) t ∧
      ∀ (Γ k : Subgroup (Multiplicative (SAdeleRing F Sf))) (m n r s : ℕ) (d : Fin s → ℕ)
        (π : Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
        (hπ : IsElemPresentation Γ k π),
        @Continuous (ElemSchwartz m n r s d) (SchwartzBruhat (Multiplicative (SAdeleRing F Sf)))
          _ t (SchwartzBruhat.ofElem Γ k π hs hπ)} :=
    ⟨lc_of_seminorm _, fun Γ k m n r s d π hs hπ => ofElem_pw_cont w hw π hs hπ⟩
  have hle : instTopologicalSpaceSchwartzBruhat (Multiplicative (SAdeleRing F Sf)) ≤ t :=
    sInf_le hmem
  have hB' := Bornology.IsVonNBounded.of_topologicalSpace_le (𝕜 := ℂ) hle hB
  obtain ⟨M, hM⟩ := bdd_of_seminorm (pw w hw) B hB'
  exact ⟨M, fun f hf x => (le_pw w hw f x).trans (hM f hf).le⟩

/-- the level of the finite components -/
noncomputable def lvl (x : SAdeleRing F Sf) : ℕ := ⌈∑ v : Sf, ‖x.2 v‖⌉₊

lemma norm_le_lvl (x : SAdeleRing F Sf) (v : Sf) : ‖x.2 v‖ ≤ lvl x := by
  have h1 : ‖x.2 v‖ ≤ ∑ v : Sf, ‖x.2 v‖ :=
    Finset.single_le_sum (f := fun v : Sf => ‖x.2 v‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ v)
  exact h1.trans (Nat.le_ceil _)

lemma adm_level (φ : ℕ → ℝ) (hφ : ∀ l, 0 ≤ φ l) : Adm (fun x : SAdeleRing F Sf => φ (lvl x)) := by
  refine ⟨fun x => hφ _, fun L => ?_⟩
  let n₀ : ℕ := ⌈(Fintype.card Sf : ℝ) * L⌉₊
  refine ⟨∑ l ∈ Finset.range (n₀ + 1), φ l, 0, Finset.sum_nonneg fun l _ => hφ l,
    fun x hx => ?_⟩
  rw [pow_zero, mul_one]
  have hsum : ∑ v : Sf, ‖x.2 v‖ ≤ (Fintype.card Sf : ℝ) * L := by
    have := Finset.sum_le_sum (s := Finset.univ) fun v _ => hx v
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at this
    exact this
  have hl : lvl x ≤ n₀ := Nat.ceil_le_ceil hsum
  exact Finset.single_le_sum (f := φ) (fun l _ => hφ l) (Finset.mem_range.2 (by omega))

lemma adm_decay (N : ℕ) : Adm (fun x : SAdeleRing F Sf => (1 + infN x.1) ^ N) := by
  refine ⟨fun x => pow_nonneg (by linarith [infN_nonneg x.1]) N, fun L => ⟨1, N, zero_le_one,
    fun x _ => by rw [one_mul]⟩⟩

/-- bounded sets are uniformly supported and uniformly rapidly decreasing -/
lemma bdd_uniform (B : Set (SAdelicSchwartz F Sf)) (hB : Bornology.IsVonNBounded ℂ B) :
    ∃ R : ℝ, (∀ f ∈ B, ∀ x : SAdeleRing F Sf, f.eval x ≠ 0 → ∀ v : Sf, ‖x.2 v‖ ≤ R) ∧
      ∀ N : ℕ, ∃ C : ℝ, ∀ f ∈ B, ∀ x : SAdeleRing F Sf, (1 + infN x.1) ^ N * ‖f.eval x‖ ≤ C := by
  have hsupp : ∃ n₀ : ℕ, ∀ f ∈ B, ∀ x : SAdeleRing F Sf, f.eval x ≠ 0 → lvl x ≤ n₀ := by
    by_contra hcon
    push Not at hcon
    choose fs hfs xs hxs hlt using hcon
    let φ : ℕ → ℝ := fun l => ∑ i ∈ Finset.range l, ((i : ℕ) : ℝ) / ‖(fs i).eval (xs i)‖
    have hφ : ∀ l, 0 ≤ φ l := fun l => Finset.sum_nonneg fun i _ => by positivity
    obtain ⟨M, hM⟩ := bdd_weight _ (adm_level φ hφ) B hB
    let i₀ : ℕ := ⌈M⌉₊ + 1
    have h1 := hM (fs i₀) (hfs i₀) (xs i₀)
    have hpos : 0 < ‖(fs i₀).eval (xs i₀)‖ := norm_pos_iff.2 (hxs i₀)
    have h2 : (i₀ : ℝ) / ‖(fs i₀).eval (xs i₀)‖ ≤ φ (lvl (xs i₀)) :=
      Finset.single_le_sum (f := fun i : ℕ => ((i : ℕ) : ℝ) / ‖(fs i).eval (xs i)‖)
        (fun i _ => by positivity) (Finset.mem_range.2 (hlt i₀))
    have h3 : (i₀ : ℝ) ≤ φ (lvl (xs i₀)) * ‖(fs i₀).eval (xs i₀)‖ := by
      rw [div_le_iff₀ hpos] at h2
      exact h2
    have h4 : M < i₀ := by
      have := Nat.le_ceil M
      have h5 : ((⌈M⌉₊ + 1 : ℕ) : ℝ) = (⌈M⌉₊ : ℝ) + 1 := by push_cast; ring
      show M < ((⌈M⌉₊ + 1 : ℕ) : ℝ)
      rw [h5]
      linarith
    have h6 : φ (lvl (xs i₀)) * ‖(fs i₀).eval (xs i₀)‖ ≤ M := h1
    linarith
  obtain ⟨n₀, hn₀⟩ := hsupp
  refine ⟨n₀, fun f hf x hx v => (norm_le_lvl x v).trans (by exact_mod_cast hn₀ f hf x hx),
    fun N => ?_⟩
  obtain ⟨M, hM⟩ := bdd_weight _ (adm_decay N) B hB
  exact ⟨M, hM⟩

end Weight

section Final

variable {F : Type*} [Field F] [NumberField F] {Sf : Finset (HeightOneSpectrum (𝓞 F))}

lemma add_pow_le_two (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (r : ℕ) :
    (a + b) ^ r ≤ 2 ^ r * (a ^ r + b ^ r) := by
  have h1 : a + b ≤ 2 * max a b := by
    have := le_max_left a b
    have := le_max_right a b
    linarith
  have h2 : (a + b) ^ r ≤ (2 * max a b) ^ r := pow_le_pow_left₀ (by positivity) h1 r
  rw [mul_pow] at h2
  have h3 : (max a b) ^ r ≤ a ^ r + b ^ r := by
    rcases le_total a b with h | h
    · rw [max_eq_right h]
      have : 0 ≤ a ^ r := pow_nonneg ha r
      linarith
    · rw [max_eq_left h]
      have : 0 ≤ b ^ r := pow_nonneg hb r
      linarith
  have h4 : (0 : ℝ) ≤ 2 ^ r := by positivity
  nlinarith

/-- uniform bound over a bounded set -/
lemma theta_unif (B : Set (SAdelicSchwartz F Sf)) (hB : Bornology.IsVonNBounded ℂ B) :
    ∃ K B' : ℝ, 0 ≤ K ∧ 0 ≤ B' ∧ ∀ f ∈ B, ∀ g : SIdeleGroup F Sf,
      ‖sLocalTheta f g‖ ≤ K * (|Real.log (sIdeleNorm Sf g)| + B') ^ rk F Sf := by
  obtain ⟨R, hR, hD⟩ := bdd_uniform B hB
  obtain ⟨C₀, hC₀⟩ := hD (rk F Sf + 2)
  obtain ⟨A, B', hA, hB', hmain⟩ := theta_main (Sf := Sf) R
  refine ⟨max C₀ 0 * A, B', mul_nonneg (le_max_right _ _) hA, hB', fun f hf g => ?_⟩
  exact (hmain f (max C₀ 0) (hR f hf) (fun x => (hC₀ f hf x).trans (le_max_left _ _)) g).2

lemma res_asym (B : Set (SAdelicSchwartz F Sf)) (hB : Bornology.IsVonNBounded ℂ B) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ f ∈ B, ∀ g : SIdeleGroup F Sf, sIdeleNorm Sf g < 1 →
      ‖sLocalTheta f g‖ ≤
        C₁ * |Real.log (sIdeleNorm Sf g)| ^
          (InfinitePlace.nrRealPlaces F + InfinitePlace.nrComplexPlaces F + Sf.card - 1) + C₂ := by
  obtain ⟨K, B', hK, hB', hθ⟩ := theta_unif B hB
  refine ⟨K * 2 ^ rk F Sf + 1, K * 2 ^ rk F Sf * B' ^ rk F Sf + 1, by positivity, by positivity,
    fun f hf g _ => ?_⟩
  have h1 := hθ f hf g
  have h2 := add_pow_le_two |Real.log (sIdeleNorm Sf g)| B' (abs_nonneg _) hB' (rk F Sf)
  have h3 : 0 ≤ |Real.log (sIdeleNorm Sf g)| ^ rk F Sf := by positivity
  have h4 : K * (|Real.log (sIdeleNorm Sf g)| + B') ^ rk F Sf ≤
      K * (2 ^ rk F Sf * (|Real.log (sIdeleNorm Sf g)| ^ rk F Sf + B' ^ rk F Sf)) :=
    mul_le_mul_of_nonneg_left h2 hK
  show ‖sLocalTheta f g‖ ≤ (K * 2 ^ rk F Sf + 1) * |Real.log (sIdeleNorm Sf g)| ^ rk F Sf +
    (K * 2 ^ rk F Sf * B' ^ rk F Sf + 1)
  nlinarith

lemma res_bdd (B : Set (SAdelicSchwartz F Sf)) (hB : Bornology.IsVonNBounded ℂ B) (ε : ℝ)
    (hε : 0 < ε) :
    ∃ C : ℝ, ∀ f ∈ B, ∀ g : SIdeleGroup F Sf, sIdeleNorm Sf g < 1 →
      ‖sLocalTheta f g‖ * sIdeleNorm Sf g ^ ε ≤ C := by
  obtain ⟨K, B', hK, hB', hθ⟩ := theta_unif B hB
  refine ⟨K * (((rk F Sf).factorial : ℝ) / ε ^ rk F Sf * Real.exp (ε * B')), fun f hf g hg => ?_⟩
  have hgpos : 0 < sIdeleNorm Sf g := sIdeleNorm_pos Sf g
  have hb := rpow_log_bound B' hB' (rk F Sf) ε hε _ hgpos hg
  have hpow0 : 0 ≤ sIdeleNorm Sf g ^ ε := (Real.rpow_pos_of_pos hgpos _).le
  calc ‖sLocalTheta f g‖ * sIdeleNorm Sf g ^ ε
      ≤ K * (|Real.log (sIdeleNorm Sf g)| + B') ^ rk F Sf * sIdeleNorm Sf g ^ ε :=
        mul_le_mul_of_nonneg_right (hθ f hf g) hpow0
    _ = K * (sIdeleNorm Sf g ^ ε * (|Real.log (sIdeleNorm Sf g)| + B') ^ rk F Sf) := by ring
    _ ≤ K * (((rk F Sf).factorial : ℝ) / ε ^ rk F Sf * Real.exp (ε * B')) :=
        mul_le_mul_of_nonneg_left hb hK

/-- the coordinates of `sDiagonal ξ` in terms of those of `sDiagonal ξ * g` -/
lemma diag_eq (ξ : F) (g : SIdeleGroup F Sf) :
    sDiagonal Sf ξ = (sDiagonal Sf ξ * (g : SAdeleRing F Sf)) *
      ((g⁻¹ : SIdeleGroup F Sf) : SAdeleRing F Sf) := by
  rw [mul_assoc, Units.mul_inv, mul_one]

/-- a summable majorant, uniform over ideles with bounded inverse -/
lemma dom_on (f : SAdelicSchwartz F Sf) (M : ℝ) : ∃ u : SUnits Sf → ℝ, Summable u ∧
    ∀ (ξ : SUnits Sf) (g : SIdeleGroup F Sf),
      (∀ w : InfinitePlace F, ‖((g⁻¹ : SIdeleGroup F Sf) : SAdeleRing F Sf).1 w‖ ≤ M) →
      (∀ v : Sf, ‖((g⁻¹ : SIdeleGroup F Sf) : SAdeleRing F Sf).2 v‖ ≤ M) →
      ‖f.eval (sDiagonal Sf ((ξ : Fˣ) : F) * (g : SAdeleRing F Sf))‖ ≤ u ξ := by
  classical
  obtain ⟨⟨R, hR⟩, hD, -⟩ := eval_good f
  let N := rk F Sf + 2
  obtain ⟨C, hC⟩ := hD N
  let M' := max M 0
  let R' := max R 0
  let C' := max C 0 * (1 + M') ^ N
  let ψ : SAdeleRing F Sf → ℝ := fun x =>
    if (∀ v : Sf, ‖x.2 v‖ ≤ R' * M') then C' / (1 + infN x.1) ^ N else 0
  have hψ0 : ∀ x, 0 ≤ ψ x := by
    intro x
    simp only [ψ]
    split_ifs
    · exact div_nonneg (by positivity) (pow_nonneg (by linarith [infN_nonneg x.1]) _)
    · exact le_rfl
  have hψs : ∀ x, ψ x ≠ 0 → ∀ v : Sf, ‖x.2 v‖ ≤ R' * M' := by
    intro x hx
    by_contra hc
    exact hx (if_neg hc)
  have hψd : ∀ x, (1 + infN x.1) ^ N * ψ x ≤ C' := by
    intro x
    have hpos : 0 < (1 + infN x.1) ^ N := pow_pos (by linarith [infN_nonneg x.1]) _
    simp only [ψ]
    split_ifs
    · rw [mul_div_cancel₀ _ hpos.ne']
    · rw [mul_zero]
      positivity
  obtain ⟨A, B', -, -, hb⟩ := theta_bound (Sf := Sf) (R' * M')
  let u : SUnits Sf → ℝ := fun ξ => ψ (sDiagonal Sf ((ξ : Fˣ) : F))
  have hu : Summable u := by
    have h1 : ∀ s : Finset (SUnits Sf),
        ∑ ξ ∈ s, u ξ ≤ C' * A * (|Real.log (sIdeleNorm Sf 1)| + B') ^ rk F Sf := by
      intro s
      have := hb ψ C' hψ0 hψs hψd 1 s
      simpa only [Units.val_one, mul_one] using this
    exact summable_of_sum_le (fun ξ => hψ0 _) h1
  refine ⟨u, hu, fun ξ g hM1 hM2 => ?_⟩
  generalize hx : sDiagonal Sf ((ξ : Fˣ) : F) * (g : SAdeleRing F Sf) = x
  by_cases h0 : f.eval x = 0
  · rw [h0, norm_zero]
    exact hψ0 _
  · have hxR := hR x h0
    have hξ := diag_eq ((ξ : Fˣ) : F) g
    rw [hx] at hξ
    have hfin : ∀ v : Sf, ‖(sDiagonal Sf ((ξ : Fˣ) : F)).2 v‖ ≤ R' * M' := by
      intro v
      rw [hξ]
      show ‖x.2 v * ((g⁻¹ : SIdeleGroup F Sf) : SAdeleRing F Sf).2 v‖ ≤ R' * M'
      rw [norm_mul]
      exact mul_le_mul ((hxR v).trans (le_max_left _ _)) ((hM2 v).trans (le_max_left _ _))
        (norm_nonneg _) (le_max_right _ _)
    have hinf : 1 + infN (sDiagonal Sf ((ξ : Fˣ) : F)).1 ≤ (1 + M') * (1 + infN x.1) := by
      have h1 : infN (sDiagonal Sf ((ξ : Fˣ) : F)).1 ≤ M' * infN x.1 := by
        rw [hξ]
        unfold infN
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun w _ => ?_
        show ‖x.1 w * ((g⁻¹ : SIdeleGroup F Sf) : SAdeleRing F Sf).1 w‖ ≤ M' * ‖x.1 w‖
        rw [norm_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right ((hM1 w).trans (le_max_left _ _)) (norm_nonneg _)
      have h2 := infN_nonneg x.1
      have h3 : (0 : ℝ) ≤ M' := le_max_right _ _
      nlinarith
    have hux : u ξ = C' / (1 + infN (sDiagonal Sf ((ξ : Fˣ) : F)).1) ^ N := by
      show ψ (sDiagonal Sf ((ξ : Fˣ) : F)) = _
      simp only [ψ]
      rw [if_pos hfin]
    rw [hux]
    have hI := infN_nonneg x.1
    have hI' := infN_nonneg (sDiagonal Sf ((ξ : Fˣ) : F)).1
    have hpos : 0 < (1 + infN x.1) ^ N := pow_pos (by linarith) _
    have hpos' : 0 < (1 + infN (sDiagonal Sf ((ξ : Fˣ) : F)).1) ^ N := pow_pos (by linarith) _
    have h1 : ‖f.eval x‖ ≤ max C 0 / (1 + infN x.1) ^ N := by
      rw [le_div_iff₀ hpos, mul_comm]
      exact (hC x).trans (le_max_left _ _)
    have h2 : (1 + infN (sDiagonal Sf ((ξ : Fˣ) : F)).1) ^ N ≤ (1 + M') ^ N * (1 + infN x.1) ^ N := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by linarith) hinf N
    have h3 : max C 0 / (1 + infN x.1) ^ N ≤
        C' / (1 + infN (sDiagonal Sf ((ξ : Fˣ) : F)).1) ^ N := by
      rw [div_le_div_iff₀ hpos hpos']
      show max C 0 * (1 + infN (sDiagonal Sf ((ξ : Fˣ) : F)).1) ^ N ≤
        max C 0 * (1 + M') ^ N * (1 + infN x.1) ^ N
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left h2 (le_max_right _ _)
    exact h1.trans h3

lemma unif_on (f : SAdelicSchwartz F Sf) (M : ℝ) (K : Set (SIdeleGroup F Sf))
    (hK : ∀ g ∈ K, (∀ w : InfinitePlace F, ‖((g⁻¹ : SIdeleGroup F Sf) : SAdeleRing F Sf).1 w‖ ≤ M) ∧
      (∀ v : Sf, ‖((g⁻¹ : SIdeleGroup F Sf) : SAdeleRing F Sf).2 v‖ ≤ M)) :
    TendstoUniformlyOn
      (fun (s : Finset (SUnits Sf)) (g : SIdeleGroup F Sf) =>
        ∑ ξ ∈ s, f.eval (sDiagonal Sf ((ξ : Fˣ) : F) * (g : SAdeleRing F Sf)))
      (sLocalTheta f) Filter.atTop K := by
  obtain ⟨u, hu, hdom⟩ := dom_on f M
  exact tendstoUniformlyOn_tsum hu fun ξ g hg => hdom ξ g (hK g hg).1 (hK g hg).2

/-- the size of the inverse of an idele -/
noncomputable def invSize (g : SIdeleGroup F Sf) : ℝ :=
  ∑ w : InfinitePlace F, ‖((g⁻¹ : SIdeleGroup F Sf) : SAdeleRing F Sf).1 w‖ +
    ∑ v : Sf, ‖((g⁻¹ : SIdeleGroup F Sf) : SAdeleRing F Sf).2 v‖

lemma invSize_continuous : Continuous (invSize : SIdeleGroup F Sf → ℝ) := by
  have hc : Continuous fun g : SIdeleGroup F Sf => ((g⁻¹ : SIdeleGroup F Sf) : SAdeleRing F Sf) :=
    Units.continuous_coe_inv
  refine Continuous.add ?_ ?_
  · exact continuous_finsetSum _ fun w _ => ((continuous_apply w).comp (continuous_fst.comp hc)).norm
  · exact continuous_finsetSum _ fun v _ => ((continuous_apply v).comp (continuous_snd.comp hc)).norm

lemma coord_le_invSize (g : SIdeleGroup F Sf) :
    (∀ w : InfinitePlace F, ‖((g⁻¹ : SIdeleGroup F Sf) : SAdeleRing F Sf).1 w‖ ≤ invSize g) ∧
      (∀ v : Sf, ‖((g⁻¹ : SIdeleGroup F Sf) : SAdeleRing F Sf).2 v‖ ≤ invSize g) := by
  have h1 : 0 ≤ ∑ w : InfinitePlace F, ‖((g⁻¹ : SIdeleGroup F Sf) : SAdeleRing F Sf).1 w‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  have h2 : 0 ≤ ∑ v : Sf, ‖((g⁻¹ : SIdeleGroup F Sf) : SAdeleRing F Sf).2 v‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨fun w => ?_, fun v => ?_⟩
  · have := Finset.single_le_sum
      (f := fun w : InfinitePlace F => ‖((g⁻¹ : SIdeleGroup F Sf) : SAdeleRing F Sf).1 w‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ w)
    unfold invSize
    linarith
  · have := Finset.single_le_sum
      (f := fun v : Sf => ‖((g⁻¹ : SIdeleGroup F Sf) : SAdeleRing F Sf).2 v‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ v)
    unfold invSize
    linarith

lemma theta_continuous (f : SAdelicSchwartz F Sf) : Continuous (sLocalTheta f) := by
  obtain ⟨-, -, hfc⟩ := eval_good f
  rw [continuous_iff_continuousAt]
  intro g₀
  let U : Set (SIdeleGroup F Sf) := {g | invSize g < invSize g₀ + 1}
  have hU : IsOpen U := isOpen_lt invSize_continuous continuous_const
  have hg₀ : g₀ ∈ U := by
    show invSize g₀ < invSize g₀ + 1
    linarith
  have hTU := unif_on f (invSize g₀ + 1) U fun g hg =>
    ⟨fun w => ((coord_le_invSize g).1 w).trans hg.le,
      fun v => ((coord_le_invSize g).2 v).trans hg.le⟩
  have hcont : ∀ s : Finset (SUnits Sf), ContinuousOn (fun g : SIdeleGroup F Sf =>
      ∑ ξ ∈ s, f.eval (sDiagonal Sf ((ξ : Fˣ) : F) * (g : SAdeleRing F Sf))) U := by
    intro s
    exact (continuous_finsetSum _ fun ξ _ =>
      hfc.comp (continuous_const.mul Units.continuous_val)).continuousOn
  have hco := hTU.continuousOn (Filter.Eventually.frequently (Filter.Eventually.of_forall hcont))
  exact hco.continuousAt (hU.mem_nhds hg₀)

lemma theta_invariant (f : SAdelicSchwartz F Sf) (η : Fˣ) (hη : η ∈ SUnits Sf)
    (g : SIdeleGroup F Sf) :
    sLocalTheta f (Units.map (sDiagonal Sf).toMonoidHom η * g) = sLocalTheta f g := by
  unfold sLocalTheta
  let η' : SUnits Sf := ⟨η, hη⟩
  let Φ : SUnits Sf → ℂ := fun ξ => f.eval (sDiagonal Sf ((ξ : Fˣ) : F) * (g : SAdeleRing F Sf))
  have h1 : ∀ ξ : SUnits Sf, f.eval (sDiagonal Sf ((ξ : Fˣ) : F) *
      ((Units.map (sDiagonal Sf).toMonoidHom η * g : SIdeleGroup F Sf) : SAdeleRing F Sf)) =
      Φ (Equiv.mulRight η' ξ) := by
    intro ξ
    show f.eval (sDiagonal Sf ((ξ : Fˣ) : F) * (sDiagonal Sf (η : F) * (g : SAdeleRing F Sf))) =
      f.eval (sDiagonal Sf (((ξ * η' : SUnits Sf) : Fˣ) : F) * (g : SAdeleRing F Sf))
    rw [diag_mul_assoc]
    rfl
  rw [tsum_congr h1]
  exact (Equiv.mulRight η').tsum_eq Φ

/-- the product formula for `ξ g` -/
lemma norm_prod_diag (ξ : Fˣ) (hξ : ξ ∈ SUnits Sf) (g : SIdeleGroup F Sf) :
    (∏ w : InfinitePlace F, ‖(sDiagonal Sf (ξ : F) * (g : SAdeleRing F Sf)).1 w‖ ^ w.mult) *
      ∏ v : Sf, ‖(sDiagonal Sf (ξ : F) * (g : SAdeleRing F Sf)).2 v‖ = sIdeleNorm Sf g := by
  simp only [norm_diag_inf, norm_diag_fin, mul_pow, Finset.prod_mul_distrib]
  have h := sProduct Sf ξ hξ
  unfold sIdeleNorm
  calc (∏ w : InfinitePlace F, w (ξ : F) ^ w.mult) *
        (∏ w : InfinitePlace F, ‖(g : SAdeleRing F Sf).1 w‖ ^ w.mult) *
      ((∏ v : Sf, ‖((ξ : F) : (v : HeightOneSpectrum (𝓞 F)).adicCompletion F)‖) *
        ∏ v : Sf, ‖(g : SAdeleRing F Sf).2 v‖)
      = ((∏ w : InfinitePlace F, w (ξ : F) ^ w.mult) *
        ∏ v : Sf, ‖((ξ : F) : (v : HeightOneSpectrum (𝓞 F)).adicCompletion F)‖) *
        ((∏ w : InfinitePlace F, ‖(g : SAdeleRing F Sf).1 w‖ ^ w.mult) *
        ∏ v : Sf, ‖(g : SAdeleRing F Sf).2 v‖) := by ring
    _ = _ := by rw [h, one_mul]

lemma log_pow_le_exp (B' : ℝ) (hB' : 0 ≤ B') (r : ℕ) (y : ℝ) (hy : 1 ≤ y) :
    (|Real.log y| + B') ^ r ≤ (r.factorial : ℝ) * Real.exp B' * y := by
  have hy0 : 0 < y := by linarith
  have hl : 0 ≤ Real.log y := Real.log_nonneg hy
  rw [abs_of_nonneg hl]
  have h1 := Real.pow_div_factorial_le_exp (Real.log y + B') (by positivity) r
  have hfac : (0 : ℝ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
  rw [div_le_iff₀ hfac, Real.exp_add, Real.exp_log hy0] at h1
  nlinarith

lemma res_decay (B : Set (SAdelicSchwartz F Sf)) (hB : Bornology.IsVonNBounded ℂ B) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f ∈ B, ∀ g : SIdeleGroup F Sf, 1 < sIdeleNorm Sf g →
      ‖sLocalTheta f g‖ ≤ C * sIdeleNorm Sf g ^ (-(N : ℤ)) := by
  classical
  obtain ⟨R, hR, hD⟩ := bdd_uniform B hB
  let R' := max R 1
  have hR'1 : 1 ≤ R' := le_max_right _ _
  let c := Fintype.card Sf
  let Mx := N + 1
  obtain ⟨C₀, hC₀⟩ := hD (rk F Sf + 2 + nn F * Mx)
  let C₁ := max C₀ 0
  obtain ⟨A, B', hA, hB', hb⟩ := theta_bound (Sf := Sf) R
  let Q : ℝ := C₁ * (R' ^ c) ^ Mx * A * ((rk F Sf).factorial * Real.exp B')
  refine ⟨Q + 1, by positivity, fun f hf g hg => ?_⟩
  have hgpos : 0 < sIdeleNorm Sf g := by linarith
  let y := sIdeleNorm Sf g
  let ψ : SAdeleRing F Sf → ℝ := fun x =>
    if y / R' ^ c ≤ (1 + infN x.1) ^ nn F then ‖f.eval x‖ else 0
  have hψ0 : ∀ x, 0 ≤ ψ x := by
    intro x
    simp only [ψ]
    split_ifs
    · exact norm_nonneg _
    · exact le_rfl
  have hψs : ∀ x, ψ x ≠ 0 → ∀ v : Sf, ‖x.2 v‖ ≤ R := by
    intro x hx
    apply hR f hf x
    intro h0
    apply hx
    simp only [ψ, h0, norm_zero, ite_self]
  have hRc : 0 < R' ^ c := pow_pos (by linarith) _
  have hψd : ∀ x, (1 + infN x.1) ^ (rk F Sf + 2) * ψ x ≤ C₁ * ((R' ^ c) ^ Mx / y ^ Mx) := by
    intro x
    have hI := infN_nonneg x.1
    have hpos : 0 < 1 + infN x.1 := by linarith
    simp only [ψ]
    split_ifs with hcond
    · have h1 : (y / R' ^ c) ^ Mx ≤ ((1 + infN x.1) ^ nn F) ^ Mx :=
        pow_le_pow_left₀ (by positivity) hcond Mx
      rw [← pow_mul, div_pow] at h1
      have h2 : (1 + infN x.1) ^ (rk F Sf + 2 + nn F * Mx) * ‖f.eval x‖ ≤ C₁ :=
        (hC₀ f hf x).trans (le_max_left _ _)
      rw [pow_add] at h2
      have hyM : 0 < y ^ Mx := pow_pos hgpos _
      have hRM : 0 < (R' ^ c) ^ Mx := pow_pos hRc _
      rw [div_le_iff₀ hRM] at h1
      rw [mul_div_assoc', le_div_iff₀ hyM]
      have h3 : 0 ≤ (1 + infN x.1) ^ (rk F Sf + 2) * ‖f.eval x‖ := by positivity
      calc (1 + infN x.1) ^ (rk F Sf + 2) * ‖f.eval x‖ * y ^ Mx
          ≤ (1 + infN x.1) ^ (rk F Sf + 2) * ‖f.eval x‖ *
            ((1 + infN x.1) ^ (nn F * Mx) * (R' ^ c) ^ Mx) :=
            mul_le_mul_of_nonneg_left h1 h3
        _ = (1 + infN x.1) ^ (rk F Sf + 2) * (1 + infN x.1) ^ (nn F * Mx) * ‖f.eval x‖ *
            (R' ^ c) ^ Mx := by ring
        _ ≤ C₁ * (R' ^ c) ^ Mx := mul_le_mul_of_nonneg_right h2 hRM.le
    · rw [mul_zero]
      positivity
  have heq : ∀ ξ : SUnits Sf, ‖f.eval (sDiagonal Sf ((ξ : Fˣ) : F) * (g : SAdeleRing F Sf))‖ =
      ψ (sDiagonal Sf ((ξ : Fˣ) : F) * (g : SAdeleRing F Sf)) := by
    intro ξ
    generalize hx : sDiagonal Sf ((ξ : Fˣ) : F) * (g : SAdeleRing F Sf) = x
    by_cases h0 : f.eval x = 0
    · simp only [ψ, h0, norm_zero, ite_self]
    · have hxR := hR f hf x h0
      have hprod := norm_prod_diag (ξ : Fˣ) ξ.2 g
      rw [hx] at hprod
      have hI := infN_nonneg x.1
      have hinf : ∏ w : InfinitePlace F, ‖x.1 w‖ ^ w.mult ≤ (1 + infN x.1) ^ nn F := by
        calc ∏ w : InfinitePlace F, ‖x.1 w‖ ^ w.mult
            ≤ ∏ w : InfinitePlace F, (1 + infN x.1) ^ w.mult :=
              Finset.prod_le_prod (fun w _ => by positivity)
                (fun w _ => pow_le_pow_left₀ (norm_nonneg _)
                  ((norm_le_infN x.1 w).trans (by linarith)) _)
          _ = (1 + infN x.1) ^ nn F := Finset.prod_pow_eq_pow_sum _ _ _
      have hfin : ∏ v : Sf, ‖x.2 v‖ ≤ R' ^ c := by
        calc ∏ v : Sf, ‖x.2 v‖ ≤ ∏ v : Sf, R' :=
              Finset.prod_le_prod (fun v _ => norm_nonneg _)
                (fun v _ => (hxR v).trans (le_max_left _ _))
          _ = R' ^ c := by rw [Finset.prod_const, Finset.card_univ]
      have hcond : y / R' ^ c ≤ (1 + infN x.1) ^ nn F := by
        rw [div_le_iff₀ hRc]
        show sIdeleNorm Sf g ≤ _
        rw [← hprod]
        exact mul_le_mul hinf hfin (Finset.prod_nonneg fun v _ => norm_nonneg _) (by positivity)
      simp only [ψ]
      rw [if_pos hcond]
  have hsum : ∀ s : Finset (SUnits Sf),
      ∑ ξ ∈ s, ‖f.eval (sDiagonal Sf ((ξ : Fˣ) : F) * (g : SAdeleRing F Sf))‖ ≤
        C₁ * ((R' ^ c) ^ Mx / y ^ Mx) * A * (|Real.log y| + B') ^ rk F Sf := by
    intro s
    rw [Finset.sum_congr rfl fun ξ _ => heq ξ]
    exact hb ψ _ hψ0 hψs hψd g s
  have hs : Summable (fun ξ : SUnits Sf =>
      ‖f.eval (sDiagonal Sf ((ξ : Fˣ) : F) * (g : SAdeleRing F Sf))‖) :=
    summable_of_sum_le (fun _ => norm_nonneg _) hsum
  have hθ : ‖sLocalTheta f g‖ ≤
      C₁ * ((R' ^ c) ^ Mx / y ^ Mx) * A * (|Real.log y| + B') ^ rk F Sf := by
    unfold sLocalTheta
    exact (norm_tsum_le_tsum_norm hs).trans (Real.tsum_le_of_sum_le (fun _ => norm_nonneg _) hsum)
  have hlog := log_pow_le_exp B' hB' (rk F Sf) y hg.le
  have hyN : 0 < y ^ N := pow_pos hgpos _
  have hzpow : sIdeleNorm Sf g ^ (-(N : ℤ)) = 1 / y ^ N := by
    rw [zpow_neg, zpow_natCast, one_div]
  rw [hzpow]
  have hyMx : y ^ Mx = y ^ N * y := pow_succ y N
  have hC₁ : 0 ≤ C₁ := le_max_right _ _
  have hfin : C₁ * ((R' ^ c) ^ Mx / y ^ Mx) * A * (|Real.log y| + B') ^ rk F Sf ≤
      Q * (1 / y ^ N) := by
    have hX : 0 ≤ C₁ * ((R' ^ c) ^ Mx / y ^ Mx) * A := by positivity
    calc C₁ * ((R' ^ c) ^ Mx / y ^ Mx) * A * (|Real.log y| + B') ^ rk F Sf
        ≤ C₁ * ((R' ^ c) ^ Mx / y ^ Mx) * A * ((rk F Sf).factorial * Real.exp B' * y) :=
          mul_le_mul_of_nonneg_left hlog hX
      _ = Q * (1 / y ^ N) := by
          rw [hyMx]
          have hy0 : y ≠ 0 := hgpos.ne'
          field_simp <;> ring
  have hQ : Q * (1 / y ^ N) ≤ (Q + 1) * (1 / y ^ N) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  linarith

lemma res_est :
    (∀ f : SAdelicSchwartz F Sf,
      (∀ g : SIdeleGroup F Sf, Summable (fun ξ : SUnits Sf =>
        ‖f.eval (sDiagonal Sf ((ξ : Fˣ) : F) * (g : SAdeleRing F Sf))‖)) ∧
      (∀ K : Set (SIdeleGroup F Sf), IsCompact K → TendstoUniformlyOn
        (fun (s : Finset (SUnits Sf)) (g : SIdeleGroup F Sf) =>
          ∑ ξ ∈ s, f.eval (sDiagonal Sf ((ξ : Fˣ) : F) * (g : SAdeleRing F Sf)))
        (sLocalTheta f) Filter.atTop K) ∧
      Continuous (sLocalTheta f) ∧
      ∀ η ∈ SUnits Sf, ∀ g : SIdeleGroup F Sf,
        sLocalTheta f (Units.map (sDiagonal Sf).toMonoidHom η * g) = sLocalTheta f g) ∧
    (∀ B : Set (SAdelicSchwartz F Sf), Bornology.IsVonNBounded ℂ B → ∀ N : ℕ,
      ∃ C : ℝ, 0 < C ∧ ∀ f ∈ B, ∀ g : SIdeleGroup F Sf, 1 < sIdeleNorm Sf g →
        ‖sLocalTheta f g‖ ≤ C * sIdeleNorm Sf g ^ (-(N : ℤ))) := by
  refine ⟨fun f => ⟨fun g => ?_, fun K hK => ?_, theta_continuous f,
    fun η hη g => theta_invariant f η hη g⟩, fun B hB N => res_decay B hB N⟩
  · obtain ⟨⟨R, hR⟩, hD, -⟩ := eval_good f
    obtain ⟨C₀, hC₀⟩ := hD (rk F Sf + 2)
    obtain ⟨A, B', -, -, hmain⟩ := theta_main (Sf := Sf) R
    exact (hmain f C₀ hR hC₀ g).1
  · obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn invSize_continuous.continuousOn
    refine unif_on f M K fun g hg => ?_
    have h1 : invSize g ≤ M := (le_abs_self _).trans (hM g hg)
    exact ⟨fun w => ((coord_le_invSize g).1 w).trans h1,
      fun v => ((coord_le_invSize g).2 v).trans h1⟩

end Final

end Aux_MasulloGRH_sLocalTheta_asymptotic_at_zero

open Aux_MasulloGRH_sLocalTheta_asymptotic_at_zero in
theorem solution (F : Type*) [Field F] [NumberField F]
    (Sf : Finset (HeightOneSpectrum (𝓞 F))) (B : Set (SAdelicSchwartz F Sf))
    (hB : Bornology.IsVonNBounded ℂ B) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ f ∈ B, ∀ g : SIdeleGroup F Sf, sIdeleNorm Sf g < 1 →
      ‖sLocalTheta f g‖ ≤
        C₁ * |Real.log (sIdeleNorm Sf g)| ^
          (InfinitePlace.nrRealPlaces F + InfinitePlace.nrComplexPlaces F + Sf.card - 1) + C₂ :=
  res_asym B hB
