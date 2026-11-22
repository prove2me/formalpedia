-- Prove2me | solution 1 for MasulloGRH.s_unit_lattice_point_count
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T06:18:54.154302+00:00
-- url     : https://prove2.me/submissions/1f862cb6-1020-42db-a890-02c88e5d78de

import Definitions.Def_MasulloGRH_SAdeles

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

open Aux_MasulloGRH_s_unit_lattice_point_count in
theorem solution (F : Type*) [Field F] [NumberField F]
    (Sf : Finset (HeightOneSpectrum (𝓞 F))) :
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
          (InfinitePlace.nrRealPlaces F + InfinitePlace.nrComplexPlaces F + Sf.card - 1)) :=
  count_bound Sf
