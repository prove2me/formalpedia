-- Prove2me | solution 1 for MasulloGRH.global_zeta_integral
-- status  : ACCEPTED   (disprove)
-- author  : @shivm
-- created : 2026-11-21T11:03:56.197793+00:00
-- url     : https://prove2.me/submissions/b42c785b-dd43-4f65-8b4c-92b6683d8e58

import Definitions.Def_MasulloGRH_ZetaIntegrals

set_option autoImplicit false
set_option linter.all false

universe u

namespace Aux_ESF
end Aux_ESF

set_option autoImplicit false

open MasulloGRH NumberField IsDedekindDomain

namespace Aux_MasulloGRH_idele_class_group_topology

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
end Aux_MasulloGRH_idele_class_group_topology

namespace Aux_LFA
open Aux_ESF

open MasulloGRH Topology Filter Set
open scoped Pointwise

noncomputable section

/-! ### compactness of sets of characters (adapted from Mathlib's local compactness proof) -/

section dualcpt

variable {X Y : Type*} [TopologicalSpace X] [Group X] [IsTopologicalGroup X]
  [UniformSpace Y] [CommGroup Y] [IsUniformGroup Y] [T0Space Y] [CompactSpace Y]

lemma cpt_of_equi (U : Set X) (V W : Set Y) (hU : IsCompact U) (hWV : W ⊆ V) (hWc : IsClosed W)
    (h : EquicontinuousAt (fun f : {f : X →* Y | Set.MapsTo f U V} ↦ (f : X → Y)) 1) :
    IsCompact {f : ContinuousMonoidHom X Y | Set.MapsTo f U W} := by
  replace h := equicontinuous_of_equicontinuousAt_one _ h
  let S1 : Set (X →* Y) := {f | Set.MapsTo f U W}
  let S2 : Set (ContinuousMonoidHom X Y) := {f | Set.MapsTo f U W}
  let S3 : Set C(X, Y) := (↑) '' S2
  let S4 : Set (X → Y) := (↑) '' S3
  replace h : Equicontinuous ((↑) : S1 → X → Y) :=
    h.comp (Subtype.map _root_.id fun f hf ↦ hf.mono_right hWV)
  have hS4 : S4 = (↑) '' S1 := by
    ext
    constructor
    · rintro ⟨-, ⟨f, hf, rfl⟩, rfl⟩
      exact ⟨f, hf, rfl⟩
    · rintro ⟨f, hf, rfl⟩
      exact ⟨⟨f, h.continuous ⟨f, hf⟩⟩, ⟨⟨f, h.continuous ⟨f, hf⟩⟩, hf, rfl⟩, rfl⟩
  replace h : Equicontinuous ((↑) : S3 → X → Y) := by
    rw [equicontinuous_iff_range, ← Set.image_eq_range] at h ⊢
    rwa [← hS4] at h
  replace hS4 : S4 = Set.pi U (fun _ ↦ W) ∩ Set.range ((↑) : (X →* Y) → (X → Y)) := by
    simp_rw [hS4, Set.ext_iff, Set.mem_image, S1, Set.mem_ofPred_eq]
    exact fun f ↦ ⟨fun ⟨g, hg, hf⟩ ↦ hf ▸ ⟨hg, g, rfl⟩, fun ⟨hg, g, hf⟩ ↦ ⟨g, hf ▸ hg, hf⟩⟩
  replace hS4 : IsClosed S4 :=
    hS4.symm ▸ (isClosed_set_pi (fun _ _ ↦ hWc)).inter (MonoidHom.isClosed_range_coe X Y)
  exact (ContinuousMonoidHom.isInducing_toContinuousMap X Y).isCompact_iff.mpr
      (ArzelaAscoli.isCompact_of_equicontinuous S3 hS4.isCompact h)

lemma equi_of_basis (U0 : Set X) (hU0o : U0 ∈ 𝓝 (1 : X)) (V : ℕ → Set Y)
    (hV : ∀ {n x}, x ∈ V n → x * x ∈ V n → x ∈ V (n + 1))
    (hVo : Filter.HasBasis (nhds 1) (fun _ ↦ True) V) :
    EquicontinuousAt (fun f : {f : X →* Y | Set.MapsTo f U0 (V 0)} ↦ (f : X → Y)) 1 := by
  let U_aux : ℕ → {S : Set X | S ∈ nhds 1} :=
    Nat.rec ⟨U0, hU0o⟩ <| fun _ S ↦ let h := exists_closed_nhds_one_inv_eq_mul_subset S.2
      ⟨Classical.choose h, (Classical.choose_spec h).1⟩
  let U : ℕ → Set X := fun n ↦ (U_aux n).1
  have hU1 : ∀ n, U n ∈ nhds 1 := fun n ↦ (U_aux n).2
  have hU2 : ∀ n, U (n + 1) * U (n + 1) ⊆ U n :=
    fun n ↦ (Classical.choose_spec (exists_closed_nhds_one_inv_eq_mul_subset (U_aux n).2)).2.2.2
  have hU3 : ∀ n, U (n + 1) ⊆ U n :=
    fun n x hx ↦ hU2 n (mul_one x ▸ Set.mul_mem_mul hx (mem_of_mem_nhds (hU1 (n + 1))))
  have hU4 : ∀ f : X →* Y, Set.MapsTo f (U 0) (V 0) → ∀ n, Set.MapsTo f (U n) (V n) := by
    intro f hf n
    induction n with
    | zero => exact hf
    | succ n ih =>
      exact fun x hx ↦ hV (ih (hU3 n hx)) (map_mul f x x ▸ ih (hU2 n (Set.mul_mem_mul hx hx)))
  rw [hVo.uniformity_of_nhds_one.equicontinuousAt_iff_right]
  refine fun n _ ↦ Filter.eventually_iff_exists_mem.mpr ⟨U n, hU1 n, fun x hx ⟨f, hf⟩ ↦ ?_⟩
  rw [Set.mem_ofPred_eq, map_one, div_one]
  exact hU4 f hf n hx

end dualcpt

/-- closed half-plane-type neighbourhood of `1` in the circle -/
def Wc : Set Circle := {z | (1 / 2 : ℝ) ≤ (z : ℂ).re}

lemma Wc_closed : IsClosed Wc :=
  isClosed_le continuous_const (Complex.continuous_re.comp continuous_subtype_val)

lemma Wo_open : IsOpen {z : Circle | (1 / 2 : ℝ) < (z : ℂ).re} :=
  isOpen_lt continuous_const (Complex.continuous_re.comp continuous_subtype_val)

lemma Wo_sub : {z : Circle | (1 / 2 : ℝ) < (z : ℂ).re} ⊆ interior Wc :=
  interior_maximal (fun z (hz : (1 / 2 : ℝ) < (z : ℂ).re) => (le_of_lt hz : (1 / 2 : ℝ) ≤ (z : ℂ).re)) Wo_open

lemma one_mem_Wo : (1 : Circle) ∈ {z : Circle | (1 / 2 : ℝ) < (z : ℂ).re} := by
  show (1 / 2 : ℝ) < ((1 : Circle) : ℂ).re
  rw [Circle.coe_one, Complex.one_re]; norm_num

lemma Wc_sub : Wc ⊆ Circle.centeredArc (Real.pi / 2) := by
  intro z hz
  rw [Circle.mem_centeredArc (by linarith [Real.pi_pos])]
  have h : 0 < (z : ℂ).re := lt_of_lt_of_le (by norm_num) hz
  exact Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl h)

lemma cpt_char {X : Type*} [TopologicalSpace X] [Group X] [IsTopologicalGroup X]
    (U : Set X) (hUc : IsCompact U) (hU1 : U ∈ 𝓝 (1 : X)) :
    IsCompact {f : ContinuousMonoidHom X Circle | Set.MapsTo f U Wc} := by
  let Vn : ℕ → Set Circle := fun n ↦ Circle.centeredArc (Real.pi / 2 ^ (n + 1))
  have hVn : ∀ n x, x ∈ Vn n ↔ |Complex.arg x| < Real.pi / 2 ^ (n + 1) :=
    fun n x ↦ Circle.mem_centeredArc (z := x)
      (div_le_self Real.pi_nonneg (one_le_pow₀ one_le_two))
  have hV : ∀ {n x}, x ∈ Vn n → x * x ∈ Vn n → x ∈ Vn (n + 1) := by
    intro n x h1 h2
    rw [hVn] at h1 h2 ⊢
    rwa [Circle.coe_mul, Complex.arg_mul x.coe_ne_zero x.coe_ne_zero,
      ← two_mul, abs_mul, abs_two, ← lt_div_iff₀' two_pos, div_div, ← pow_succ] at h2
    apply Set.Ioo_subset_Ioc_self
    rw [← two_mul, Set.mem_Ioo, ← abs_lt, abs_mul, abs_two, ← lt_div_iff₀' two_pos]
    refine h1.trans_le ?_
    gcongr
    exact le_self_pow₀ one_le_two n.succ_ne_zero
  have hVo : Filter.HasBasis (nhds (1 : Circle)) (fun _ ↦ True) Vn := by
    simpa [Vn] using Circle.hasBasis_centeredArc_div_two_pow
  have h0 : Vn 0 = Circle.centeredArc (Real.pi / 2) := by simp [Vn]
  have he := equi_of_basis U hU1 Vn hV hVo
  rw [h0] at he
  exact cpt_of_equi U _ Wc hUc Wc_sub Wc_closed he

/-! ### the annihilator as a subgroup -/

section annsub

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- the annihilator as a subgroup of the dual -/
def annSub (k : Subgroup G) : Subgroup (PontryaginDual G) where
  carrier := annihilator k
  mul_mem' {χ ψ} hχ hψ x hx := by
    show χ x * ψ x = 1
    rw [hχ x hx, hψ x hx, one_mul]
  one_mem' x _ := rfl
  inv_mem' {χ} hχ x hx := by
    show (χ x)⁻¹ = 1
    rw [hχ x hx, inv_one]

lemma annihilator_closed (k : Subgroup G) : IsClosed (annihilator k) := by
  have : annihilator k = ⋂ x ∈ k, {χ : PontryaginDual G | χ x = 1} := by
    ext χ; simp [annihilator]
  rw [this]
  refine isClosed_biInter fun x _ => isClosed_eq ?_ continuous_const
  exact (continuous_eval_const x : Continuous fun χ : ContinuousMonoidHom G Circle => χ x)

lemma annihilator_open_of_compact (k : Subgroup G) (hk : IsCompact (k : Set G)) :
    IsOpen (annihilator k) := by
  let V : Set (PontryaginDual G) :=
    {ψ | Set.MapsTo ψ (k : Set G) (Circle.centeredArc (Real.pi / 2))}
  have hVopen : IsOpen V :=
    isOpen_induced (ContinuousMap.isOpen_setOfPred_mapsTo hk (Circle.isOpen_centeredArc _))
  have hVeq : V = annihilator k := by
    ext ψ
    refine ⟨fun hψ a ha ↦ ?_, fun hψ a ha ↦ ?_⟩
    · refine Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two fun n _ ↦ ?_
      rw [← map_pow]
      exact hψ (k.pow_mem ha n)
    · rw [hψ a ha, Circle.mem_centeredArc (by linarith [Real.pi_pos])]
      simp [Real.pi_pos]
  rw [← hVeq]; exact hVopen

end annsub

/-! ### the generic setting -/

/-- a group `A ≅ ℝ^m × B`, with a filtration of `B` by compact open subgroups -/
structure Setup (A : Type*) [AddCommGroup A] [TopologicalSpace A] (B : Type*) [AddCommGroup B]
    [TopologicalSpace B] (m : ℕ) where
  e : ((Fin m → ℝ) × B) ≃+ A
  he : Continuous e
  hes : Continuous e.symm
  L : ℕ → AddSubgroup B
  M : ℕ → AddSubgroup B
  L_open : ∀ N, IsOpen (L N : Set B)
  L_cpt : ∀ N, IsCompact (L N : Set B)
  M_open : ∀ N, IsOpen (M N : Set B)
  M_cpt : ∀ N, IsCompact (M N : Set B)
  L_mono : Monotone L
  M_anti : Antitone M
  ML : ∀ N, M N ≤ L N
  L_cov : ∀ y, ∃ N, y ∈ L N
  M_small : ∀ W ∈ 𝓝 (0 : B), ∃ N, (M N : Set B) ⊆ W

namespace Setup

variable {A : Type*} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  {B : Type*} [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B] {m : ℕ}
  (S : Setup A B m)

/-- vector coordinate -/
def X (z : Multiplicative A) : Fin m → ℝ := (S.e.symm (Multiplicative.toAdd z)).1
/-- `B` coordinate -/
def Y (z : Multiplicative A) : B := (S.e.symm (Multiplicative.toAdd z)).2
/-- the point with coordinates `(x, y)` -/
def emb (x : Fin m → ℝ) (y : B) : Multiplicative A := Multiplicative.ofAdd (S.e (x, y))

@[simp] lemma X_emb (x y) : S.X (S.emb x y) = x := by simp [X, emb]
@[simp] lemma Y_emb (x y) : S.Y (S.emb x y) = y := by simp [Y, emb]
lemma emb_XY (z : Multiplicative A) : S.emb (S.X z) (S.Y z) = z := by
  simp [X, Y, emb]
lemma emb_mul (x y x' y') : S.emb x y * S.emb x' y' = S.emb (x + x') (y + y') := by
  simp only [emb, ← ofAdd_add, ← map_add, Prod.mk_add_mk]
@[simp] lemma X_mul (z w) : S.X (z * w) = S.X z + S.X w := by
  simp [X, toAdd_mul, map_add]
@[simp] lemma Y_mul (z w) : S.Y (z * w) = S.Y z + S.Y w := by
  simp [Y, toAdd_mul, map_add]
@[simp] lemma X_one : S.X 1 = 0 := by simp [X]
@[simp] lemma Y_one : S.Y 1 = 0 := by simp [Y]
@[simp] lemma X_inv (z) : S.X z⁻¹ = -S.X z := by simp [X, toAdd_inv, map_neg]
@[simp] lemma Y_inv (z) : S.Y z⁻¹ = -S.Y z := by simp [Y, toAdd_inv, map_neg]
@[simp] lemma X_pow (z) (n : ℕ) : S.X (z ^ n) = n • S.X z := by simp [X, toAdd_pow, map_nsmul]
@[simp] lemma Y_pow (z) (n : ℕ) : S.Y (z ^ n) = n • S.Y z := by simp [Y, toAdd_pow, map_nsmul]
lemma emb_zero : S.emb 0 0 = 1 := by simp [emb]
lemma emb_split (x y) : S.emb x y = S.emb x 0 * S.emb 0 y := by rw [emb_mul]; simp
lemma emb_pow (x y) (n : ℕ) : S.emb x y ^ n = S.emb (n • x) (n • y) := by
  conv_lhs => rw [← S.emb_XY (S.emb x y ^ n)]
  simp
lemma ext_XY {z w : Multiplicative A} (h1 : S.X z = S.X w) (h2 : S.Y z = S.Y w) : z = w := by
  rw [← S.emb_XY z, ← S.emb_XY w, h1, h2]

lemma cont_X : Continuous S.X :=
  continuous_fst.comp (S.hes.comp continuous_toAdd)
lemma cont_Y : Continuous S.Y :=
  continuous_snd.comp (S.hes.comp continuous_toAdd)
lemma cont_emb : Continuous (fun p : (Fin m → ℝ) × B => S.emb p.1 p.2) :=
  continuous_ofAdd.comp S.he

/-- the stage groups `Γ_N = ℝ^m × L_N` -/
def Gam (N : ℕ) : Subgroup (Multiplicative A) where
  carrier := {z | S.Y z ∈ S.L N}
  mul_mem' {z w} hz hw := by
    show S.Y (z * w) ∈ S.L N
    rw [Y_mul]; exact add_mem hz hw
  one_mem' := by show S.Y 1 ∈ S.L N; rw [Y_one]; exact zero_mem _
  inv_mem' {z} hz := by show S.Y z⁻¹ ∈ S.L N; rw [Y_inv]; exact neg_mem hz

/-- the stage groups `k_N = 0 × M_N` -/
def Kk (N : ℕ) : Subgroup (Multiplicative A) where
  carrier := {z | S.X z = 0 ∧ S.Y z ∈ S.M N}
  mul_mem' {z w} hz hw := by
    refine ⟨?_, ?_⟩
    · rw [X_mul, hz.1, hw.1, add_zero]
    · rw [Y_mul]; exact add_mem hz.2 hw.2
  one_mem' := ⟨S.X_one, by rw [Y_one]; exact zero_mem _⟩
  inv_mem' {z} hz := ⟨by rw [X_inv, hz.1, neg_zero], by rw [Y_inv]; exact neg_mem hz.2⟩

lemma mem_Gam {N z} : z ∈ S.Gam N ↔ S.Y z ∈ S.L N := Iff.rfl
lemma mem_Kk {N z} : z ∈ S.Kk N ↔ S.X z = 0 ∧ S.Y z ∈ S.M N := Iff.rfl

lemma Kk_le (N : ℕ) : S.Kk N ≤ S.Gam N := fun _ hz => S.ML N hz.2

lemma Gam_open (N : ℕ) : IsOpen (S.Gam N : Set (Multiplicative A)) :=
  (S.L_open N).preimage S.cont_Y

lemma M_closed (N : ℕ) : IsClosed (S.M N : Set B) :=
  AddSubgroup.isClosed_of_isOpen _ (S.M_open N)

lemma Kk_closed (N : ℕ) : IsClosed (S.Kk N : Set (Multiplicative A)) :=
  (isClosed_eq S.cont_X continuous_const).inter ((S.M_closed N).preimage S.cont_Y)

lemma Kk_eq_image (N : ℕ) : (S.Kk N : Set (Multiplicative A)) =
    (fun p : (Fin m → ℝ) × B => S.emb p.1 p.2) '' ({0} ×ˢ (S.M N : Set B)) := by
  ext z
  constructor
  · intro hz
    exact ⟨(S.X z, S.Y z), ⟨hz.1, hz.2⟩, S.emb_XY z⟩
  · rintro ⟨p, ⟨h1, h2⟩, rfl⟩
    exact ⟨by simpa using h1, by simpa using h2⟩

lemma Kk_cpt (N : ℕ) : IsCompact (S.Kk N : Set (Multiplicative A)) := by
  rw [Kk_eq_image]
  exact (isCompact_singleton.prod (S.M_cpt N)).image S.cont_emb

/-- `x ↦ x / n` -/
lemma emb_div (x : Fin m → ℝ) (n : ℕ) (hn : n ≠ 0) :
    S.emb x 0 = S.emb ((n : ℝ)⁻¹ • x) 0 ^ n := by
  rw [emb_pow, smul_zero, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
    mul_inv_cancel₀ (by exact_mod_cast hn), one_smul]

lemma Gam_cg (N : ℕ) : IsCompactlyGeneratedSubgroup (S.Gam N) := by
  let f := fun p : (Fin m → ℝ) × B => S.emb p.1 p.2
  refine ⟨f '' (Metric.closedBall 0 1 ×ˢ (S.L N : Set B)),
    ((isCompact_closedBall _ _).prod (S.L_cpt N)).image S.cont_emb, ?_,
    ⟨{z | ‖S.X z‖ < 1}, ?_, ?_⟩, ?_⟩
  · rintro _ ⟨p, ⟨_, h2⟩, rfl⟩
    show S.Y (S.emb p.1 p.2) ∈ S.L N
    simpa using h2
  · refine (isOpen_lt (continuous_norm.comp S.cont_X) continuous_const).mem_nhds ?_
    show ‖S.X 1‖ < 1
    simp
  · rintro z ⟨h1, h2⟩
    exact ⟨(S.X z, S.Y z), ⟨mem_closedBall_zero_iff.2 (le_of_lt h1), h2⟩, S.emb_XY z⟩
  · refine le_antisymm ((Subgroup.closure_le _).2 ?_) ?_
    · rintro _ ⟨p, ⟨_, h2⟩, rfl⟩
      show S.Y (S.emb p.1 p.2) ∈ S.L N
      simpa using h2
    · intro z hz
      obtain ⟨n, hn⟩ := exists_nat_gt ‖S.X z‖
      have hn0 : n ≠ 0 := by
        rintro rfl; simp at hn; exact absurd hn (not_lt.2 (norm_nonneg _))
      rw [← S.emb_XY z, S.emb_split, S.emb_div _ n hn0]
      refine mul_mem (pow_mem (Subgroup.subset_closure (show S.emb ((n : ℝ)⁻¹ • S.X z) 0 ∈
        f '' (Metric.closedBall 0 1 ×ˢ (S.L N : Set B)) from ⟨((n : ℝ)⁻¹ • S.X z, 0), ⟨?_, zero_mem _⟩,
        rfl⟩)) _) (Subgroup.subset_closure (show S.emb 0 (S.Y z) ∈
        f '' (Metric.closedBall 0 1 ×ˢ (S.L N : Set B)) from ⟨(0, S.Y z), ⟨by simp, hz⟩, rfl⟩))
      rw [mem_closedBall_zero_iff, norm_smul, norm_inv, Real.norm_natCast]
      have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
      rw [inv_mul_le_iff₀ hnpos, mul_one]; exact le_of_lt hn

/-- the endomorphism `z ↦ (0, Y z)` -/
def Ef : ContinuousMonoidHom (Multiplicative A) (Multiplicative A) where
  toFun z := S.emb 0 (S.Y z)
  map_one' := by simp [emb_zero]
  map_mul' z w := by simp [emb_mul]
  continuous_toFun := S.cont_emb.comp (continuous_const.prodMk S.cont_Y)

/-- the endomorphism `z ↦ (X z / n, 0)` -/
def En (n : ℕ) : ContinuousMonoidHom (Multiplicative A) (Multiplicative A) where
  toFun z := S.emb ((n : ℝ)⁻¹ • S.X z) 0
  map_one' := by simp [emb_zero]
  map_mul' z w := by simp [emb_mul, smul_add]
  continuous_toFun := by
    exact S.cont_emb.comp (((S.cont_X.const_smul ((n : ℝ)⁻¹)).prodMk continuous_const :
      Continuous fun z => (((n : ℝ)⁻¹ • S.X z), (0 : B))))

lemma ann_cg (N : ℕ) : ∃ H : Subgroup (PontryaginDual (Multiplicative A)),
    (H : Set (PontryaginDual (Multiplicative A))) = annihilator (S.Kk N) ∧
      IsCompactlyGeneratedSubgroup H := by
  let K : Set (Multiplicative A) := {z | ‖S.X z‖ ≤ 1 ∧ S.Y z ∈ S.M N}
  have hKeq : K = (fun p : (Fin m → ℝ) × B => S.emb p.1 p.2) ''
      (Metric.closedBall 0 1 ×ˢ (S.M N : Set B)) := by
    ext z
    constructor
    · intro hz; exact ⟨(S.X z, S.Y z), ⟨mem_closedBall_zero_iff.2 hz.1, hz.2⟩, S.emb_XY z⟩
    · rintro ⟨p, ⟨h1, h2⟩, rfl⟩
      exact ⟨by simpa using mem_closedBall_zero_iff.1 h1, by simpa using h2⟩
  have hKc : IsCompact K := by
    rw [hKeq]; exact ((isCompact_closedBall _ _).prod (S.M_cpt N)).image S.cont_emb
  have hK1 : K ∈ 𝓝 (1 : Multiplicative A) := by
    have hO : IsOpen {z : Multiplicative A | ‖S.X z‖ < 1 ∧ S.Y z ∈ S.M N} :=
      (isOpen_lt (continuous_norm.comp S.cont_X) continuous_const).inter
        ((S.M_open N).preimage S.cont_Y)
    refine Filter.mem_of_superset (hO.mem_nhds ⟨by simp, by simp [zero_mem]⟩) ?_
    rintro z ⟨h1, h2⟩; exact ⟨le_of_lt h1, h2⟩
  let H := annSub (S.Kk N)
  let C : Set (PontryaginDual (Multiplicative A)) :=
    {χ | Set.MapsTo χ K Wc} ∩ annihilator (S.Kk N)
  refine ⟨H, rfl, C,
    (cpt_char K hKc hK1).inter_right (annihilator_closed _), fun _ h => h.2,
    ⟨{χ | Set.MapsTo χ K (interior Wc)}, ?_, ?_⟩, ?_⟩
  · refine IsOpen.mem_nhds (isOpen_induced (ContinuousMap.isOpen_setOfPred_mapsTo hKc
      isOpen_interior)) ?_
    intro z _
    exact Wo_sub one_mem_Wo
  · rintro χ ⟨h1, h2⟩
    exact ⟨fun z hz => interior_subset (h1 hz), h2⟩
  · refine le_antisymm ((Subgroup.closure_le _).2 fun χ h => h.2) ?_
    intro χ hχ
    -- continuity of `x ↦ χ (x, 0)` at `0`
    have hc : Continuous fun x : Fin m → ℝ => χ (S.emb x 0) :=
      χ.continuous.comp (S.cont_emb.comp (continuous_id.prodMk continuous_const))
    have hev : ∀ᶠ x in 𝓝 (0 : Fin m → ℝ), χ (S.emb x 0) ∈ {z : Circle | (1 / 2 : ℝ) < (z : ℂ).re} := by
      refine hc.continuousAt.preimage_mem_nhds (Wo_open.mem_nhds ?_)
      rw [emb_zero, map_one]; exact one_mem_Wo
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
    let χf : PontryaginDual (Multiplicative A) := χ.comp S.Ef
    let ψ : PontryaginDual (Multiplicative A) := χ.comp (S.En (n + 1))
    have hEf : ∀ z, S.Ef z = S.emb 0 (S.Y z) := fun _ => rfl
    have hEn : ∀ z, S.En (n + 1) z = S.emb (((n + 1 : ℕ) : ℝ)⁻¹ • S.X z) 0 := fun _ => rfl
    have hfac : χ = χf * ψ ^ (n + 1) := by
      refine PontryaginDual.ext fun z => ?_
      have h1 : (χf * ψ ^ (n + 1)) z = χf z * (ψ z) ^ (n + 1) :=
        (ContinuousMonoidHom.mul_apply (E := Circle) χf (ψ ^ (n + 1)) z).trans
          (congrArg (χf z * ·) (ContinuousMonoidHom.pow_apply (E := Circle) ψ (n + 1) z))
      rw [h1]
      show χ z = χ (S.Ef z) * χ (S.En (n + 1) z) ^ (n + 1)
      rw [hEf, hEn, ← map_pow, ← S.emb_div _ _ (Nat.succ_ne_zero n), ← map_mul, mul_comm,
        ← S.emb_split, S.emb_XY]
    have hχf : χf ∈ C := by
      refine ⟨fun z hz => ?_, fun z hz => ?_⟩
      · have : S.Ef z ∈ S.Kk N := ⟨by simp [hEf], by simpa [hEf] using hz.2⟩
        show χ (S.Ef z) ∈ Wc
        rw [hχ _ this]
        show (1 / 2 : ℝ) ≤ ((1 : Circle) : ℂ).re
        rw [Circle.coe_one, Complex.one_re]; norm_num
      · have : S.Ef z ∈ S.Kk N := ⟨by simp [hEf], by simpa [hEf] using hz.2⟩
        exact hχ _ this
    have hψ : ψ ∈ C := by
      refine ⟨fun z hz => ?_, fun z hz => ?_⟩
      · show χ (S.En (n + 1) z) ∈ Wc
        rw [hEn]
        have hd : dist ((((n + 1 : ℕ) : ℝ))⁻¹ • S.X z) 0 < δ := by
          rw [dist_zero_right, norm_smul, norm_inv, Real.norm_natCast]
          calc (((n + 1 : ℕ) : ℝ))⁻¹ * ‖S.X z‖ ≤ (((n + 1 : ℕ) : ℝ))⁻¹ * 1 :=
                mul_le_mul_of_nonneg_left hz.1 (by positivity)
            _ = 1 / ((n : ℝ) + 1) := by push_cast; ring
            _ < δ := hn
        have hb := hball hd
        simp only [Set.mem_setOf_eq] at hb
        exact hb.le
      · show χ (S.En (n + 1) z) = 1
        rw [hEn, hz.1, smul_zero, emb_zero, map_one]
    rw [hfac]
    exact mul_mem (Subgroup.subset_closure hχf) (pow_mem (Subgroup.subset_closure hψ) _)

lemma Kk_good (N : ℕ) : IsGoodSubgroup (S.Kk N) :=
  ⟨S.Kk_closed N, annihilator_open_of_compact _ (S.Kk_cpt N), S.ann_cg N⟩

lemma stage_sp (N : ℕ) : IsStructuralPair (S.Gam N) (S.Kk N) :=
  ⟨S.Gam_open N, S.Gam_cg N, S.Kk_good N, S.Kk_le N⟩

end Setup

end

end Aux_LFA

namespace Aux_LFA
open Aux_ESF

open MasulloGRH Topology Filter Set

noncomputable section

lemma fin_struct (Q : Type*) [AddCommGroup Q] [Finite Q] :
    ∃ (s : ℕ) (d : Fin s → ℕ), (∀ i, d i ≠ 0) ∧ Nonempty (Q ≃+ ((i : Fin s) → ZMod (d i))) := by
  obtain ⟨ι, fι, p, hp, ex, ⟨f⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite Q
  let σ := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun j => p (σ.symm j) ^ ex (σ.symm j), fun j =>
    pow_ne_zero _ (hp _).ne_zero, ⟨?_⟩⟩
  exact (f.trans (DirectSum.linearEquivFunOnFintype ℤ ι (fun i => ZMod (p i ^ ex i))).toAddEquiv).trans
    (RingEquiv.piCongrLeft' (fun i => ZMod (p i ^ ex i)) σ).toAddEquiv

namespace Setup

variable {A : Type*} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  {B : Type*} [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B] {m : ℕ}
  (S : Setup A B m)

/-- the finite quotient `L_N / M_N` -/
abbrev Q (N : ℕ) : Type _ := ↥(S.L N) ⧸ (S.M N).addSubgroupOf (S.L N)

instance finQ (N : ℕ) : Finite (S.Q N) := by
  haveI : CompactSpace ↥(S.L N) := isCompact_iff_compactSpace.mp (S.L_cpt N)
  exact AddSubgroup.quotient_finite_of_isOpen _ ((S.M_open N).preimage continuous_subtype_val)

lemma ex_struct (N : ℕ) : ∃ (s : ℕ) (d : Fin s → ℕ), (∀ i, d i ≠ 0) ∧
    Nonempty (S.Q N ≃+ ((i : Fin s) → ZMod (d i))) := fin_struct _

/-- number of cyclic factors -/
def sN (N : ℕ) : ℕ := (S.ex_struct N).choose
/-- orders -/
def dN (N : ℕ) : Fin (S.sN N) → ℕ := (S.ex_struct N).choose_spec.choose
lemma hdN (N : ℕ) (i) : S.dN N i ≠ 0 := (S.ex_struct N).choose_spec.choose_spec.1 i
instance neZ (N : ℕ) (i) : NeZero (S.dN N i) := ⟨S.hdN N i⟩
/-- the structure isomorphism -/
def eps (N : ℕ) : S.Q N ≃+ ((i : Fin (S.sN N)) → ZMod (S.dN N i)) :=
  Classical.choice (S.ex_struct N).choose_spec.choose_spec.2

/-- the finite coordinate -/
def del (N : ℕ) (y : ↥(S.L N)) : (i : Fin (S.sN N)) → ZMod (S.dN N i) :=
  S.eps N (QuotientAddGroup.mk y)

lemma del_add (N : ℕ) (y y' : ↥(S.L N)) : S.del N (y + y') = S.del N y + S.del N y' := by
  simp [del, QuotientAddGroup.mk_add]

lemma del_eq_iff (N : ℕ) (y y' : ↥(S.L N)) :
    S.del N y = S.del N y' ↔ ((y' : B) - y) ∈ S.M N := by
  unfold del
  rw [(S.eps N).injective.eq_iff, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
  simp [sub_eq_neg_add]

lemma del_zero_iff (N : ℕ) (y : ↥(S.L N)) : S.del N y = 0 ↔ (y : B) ∈ S.M N := by
  have h := S.del_eq_iff N 0 y
  have h0 : S.del N 0 = 0 := by simp [del]
  rw [h0] at h
  rw [eq_comm, h]; simp

lemma del_surj (N : ℕ) : Function.Surjective (S.del N) := by
  intro b
  obtain ⟨q, hq⟩ := (S.eps N).surjective b
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective q
  exact ⟨y, hq⟩

/-! ### nested sets of representatives -/

/-- `R` is a set of representatives of `L_N / M_N` -/
def IsRep (N : ℕ) (R : Set B) : Prop :=
  R ⊆ S.L N ∧ ∀ y ∈ S.L N, ∃! r, r ∈ R ∧ y - r ∈ S.M N

lemma ext_rep (N : ℕ) (T : Set B) (hT : T ⊆ S.L N)
    (hTp : ∀ a ∈ T, ∀ b ∈ T, a - b ∈ S.M N → a = b) :
    ∃ R, T ⊆ R ∧ S.IsRep N R := by
  classical
  let q : B → B ⧸ S.M N := QuotientAddGroup.mk
  have hq : ∀ a b, q a = q b ↔ a - b ∈ S.M N := by
    intro a b
    rw [QuotientAddGroup.eq]
    constructor
    · intro h; have := neg_mem h; simpa [sub_eq_add_neg, add_comm] using this
    · intro h; have := neg_mem h; simpa [sub_eq_add_neg, add_comm] using this
  let R : Set B := T ∪ {r | r ∈ S.L N ∧ (∀ t ∈ T, q t ≠ q r) ∧ (q r).out = r}
  refine ⟨R, subset_union_left, ?_, ?_⟩
  · rintro r (hr | ⟨hr, -, -⟩)
    · exact hT hr
    · exact hr
  · intro y hy
    by_cases hex : ∃ t ∈ T, q t = q y
    · obtain ⟨t, ht, hty⟩ := hex
      refine ⟨t, ⟨Or.inl ht, (hq y t).1 hty.symm⟩, ?_⟩
      rintro r ⟨hr | ⟨_, hr2, _⟩, hyr⟩
      · exact hTp r hr t ht (by
          have h1 := (hq y r).2 hyr
          exact (hq r t).1 (h1.symm.trans hty.symm))
      · exact absurd (hty.trans ((hq y r).2 hyr)) (hr2 t ht)
    · simp only [not_exists, not_and] at hex
      have hout : q (q y).out = q y := by simp [q]
      refine ⟨(q y).out, ⟨Or.inr ⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩
      · have h1 : y - (q y).out ∈ S.M N := (hq y _).1 hout.symm
        have h2 : (q y).out = y - (y - (q y).out) := by abel
        rw [h2]; exact sub_mem hy (S.ML N h1)
      · intro t ht; rw [hout]; exact hex t ht
      · rw [hout]
      · exact (hq y _).1 hout.symm
      · rintro r ⟨hr | ⟨_, _, hr3⟩, hyr⟩
        · exact absurd ((hq y r).2 hyr).symm (hex r hr)
        · rw [← hr3, (hq y r).2 hyr]

lemma isRep_succ {N : ℕ} {R : Set B} (hR : S.IsRep N R) :
    ∃ R', R ⊆ R' ∧ S.IsRep (N + 1) R' := by
  refine S.ext_rep (N + 1) R (hR.1.trans (S.L_mono (Nat.le_succ N))) fun a ha b hb hab => ?_
  have hab' : a - b ∈ S.M N := S.M_anti (Nat.le_succ N) hab
  obtain ⟨r, _, hr⟩ := hR.2 a (hR.1 ha)
  have h1 := hr a ⟨ha, by simp [zero_mem]⟩
  have h2 := hr b ⟨hb, hab'⟩
  rw [h1, h2]

lemma isRep_zero : ∃ R, S.IsRep 0 R := by
  obtain ⟨R, -, h⟩ := S.ext_rep 0 ∅ (empty_subset _) (by simp)
  exact ⟨R, h⟩

/-- the sequence of nested representative sets -/
def RR : (N : ℕ) → {R : Set B // S.IsRep N R}
  | 0 => ⟨S.isRep_zero.choose, S.isRep_zero.choose_spec⟩
  | N + 1 => ⟨(S.isRep_succ (RR N).2).choose, (S.isRep_succ (RR N).2).choose_spec.2⟩

lemma RR_succ (N : ℕ) : (S.RR N).1 ⊆ (S.RR (N + 1)).1 := by
  show _ ⊆ (S.isRep_succ (S.RR N).2).choose
  exact (S.isRep_succ (S.RR N).2).choose_spec.1

lemma RR_mono {N M : ℕ} (h : N ≤ M) : (S.RR N).1 ⊆ (S.RR M).1 := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (S.RR_succ _)

/-- the representative of `b ∈ L_N/M_N` -/
def rep (N : ℕ) (b : (i : Fin (S.sN N)) → ZMod (S.dN N i)) : B :=
  ((S.RR N).2.2 _ ((S.del_surj N b).choose).2).exists.choose

lemma rep_spec (N : ℕ) (b) : S.rep N b ∈ (S.RR N).1 ∧
    (((S.del_surj N b).choose : B) - S.rep N b) ∈ S.M N :=
  ((S.RR N).2.2 _ ((S.del_surj N b).choose).2).exists.choose_spec

lemma rep_mem (N : ℕ) (b) : S.rep N b ∈ S.L N := (S.RR N).2.1 (S.rep_spec N b).1

lemma del_rep (N : ℕ) (b) : S.del N ⟨S.rep N b, S.rep_mem N b⟩ = b := by
  have h := (S.del_eq_iff N ⟨S.rep N b, S.rep_mem N b⟩ (S.del_surj N b).choose).2
    (S.rep_spec N b).2
  rw [h]; exact (S.del_surj N b).choose_spec

lemma rep_del_of_mem (N : ℕ) (y : B) (hy : y ∈ (S.RR N).1) :
    S.rep N (S.del N ⟨y, (S.RR N).2.1 hy⟩) = y := by
  set b := S.del N ⟨y, (S.RR N).2.1 hy⟩
  have h1 : ((S.del_surj N b).choose : B) - y ∈ S.M N :=
    (S.del_eq_iff N ⟨y, (S.RR N).2.1 hy⟩ (S.del_surj N b).choose).1
      ((S.del_surj N b).choose_spec).symm
  obtain ⟨r, _, hr⟩ := (S.RR N).2.2 _ ((S.del_surj N b).choose).2
  rw [hr _ (S.rep_spec N b), hr _ ⟨hy, h1⟩]

lemma rep_nested {N M : ℕ} (h : N ≤ M) (b) :
    S.rep M (S.del M ⟨S.rep N b, S.L_mono h (S.rep_mem N b)⟩) = S.rep N b :=
  S.rep_del_of_mem M _ (S.RR_mono h (S.rep_spec N b).1)

/-! ### the presentations of the stages -/

/-- the presentation `Γ_N → ℝ^m × ∏ ℤ/d_i` -/
def pres (N : ℕ) : S.Gam N →* Multiplicative (ElemGroup m 0 0 (S.sN N) (S.dN N)) where
  toFun z := Multiplicative.ofAdd (S.X z, 0, 0, S.del N ⟨S.Y z, z.2⟩)
  map_one' := by
    have h : S.del N ⟨S.Y ((1 : S.Gam N) : Multiplicative A), (1 : S.Gam N).2⟩ = 0 := by
      rw [del_zero_iff]; show S.Y 1 ∈ S.M N; rw [Y_one]; exact zero_mem _
    simp only [OneMemClass.coe_one, X_one] at h ⊢
    rw [h]; rfl
  map_mul' z w := by
    have h : S.del N ⟨S.Y ((z * w : S.Gam N) : Multiplicative A), (z * w).2⟩ =
        S.del N ⟨S.Y z, z.2⟩ + S.del N ⟨S.Y w, w.2⟩ := by
      rw [← del_add]; congr 1; apply Subtype.ext; simp
    rw [h]
    apply Multiplicative.toAdd.injective
    simp only [toAdd_ofAdd, toAdd_mul, Subgroup.coe_mul, X_mul, Prod.mk_add_mk, add_zero]

lemma pres_apply (N : ℕ) (z : S.Gam N) :
    Multiplicative.toAdd (S.pres N z) = (S.X z, 0, 0, S.del N ⟨S.Y z, z.2⟩) := rfl

/-- the section of the presentation -/
def sec (N : ℕ) (q : ElemGroup m 0 0 (S.sN N) (S.dN N)) : Multiplicative A :=
  S.emb q.1 (S.rep N q.2.2.2)

lemma sec_mem (N : ℕ) (q) : S.sec N q ∈ S.Gam N := by
  show S.Y (S.emb _ _) ∈ S.L N; rw [Y_emb]; exact S.rep_mem N _

lemma pres_sec (N : ℕ) (q) : Multiplicative.toAdd (S.pres N ⟨S.sec N q, S.sec_mem N q⟩) = q := by
  rw [pres_apply]
  refine Prod.ext ?_ (Prod.ext (Subsingleton.elim _ _) (Prod.ext (Subsingleton.elim _ _) ?_))
  · simp [sec]
  · show S.del N _ = q.2.2.2
    have : (⟨S.Y (S.sec N q), S.sec_mem N q⟩ : ↥(S.L N)) =
        ⟨S.rep N q.2.2.2, S.rep_mem N q.2.2.2⟩ := Subtype.ext (by simp [sec])
    rw [this, del_rep]

lemma cont_del (N : ℕ) : Continuous fun z : S.Gam N => S.del N ⟨S.Y z, z.2⟩ := by
  rw [continuous_discrete_rng]
  intro b
  obtain ⟨y0, hy0⟩ := S.del_surj N b
  have : (fun z : S.Gam N => S.del N ⟨S.Y z, z.2⟩) ⁻¹' {b} =
      Subtype.val ⁻¹' (S.Y ⁻¹' ((fun y => y - (y0 : B)) ⁻¹' (S.M N : Set B))) := by
    ext z
    simp only [mem_preimage, mem_singleton_iff]
    rw [← hy0, del_eq_iff]
    show (y0 : B) - S.Y z ∈ S.M N ↔ S.Y z - (y0 : B) ∈ S.M N
    rw [← neg_sub, neg_mem_iff]
  rw [this]
  exact (((S.M_open N).preimage (continuous_id.sub continuous_const)).preimage S.cont_Y).preimage
    continuous_subtype_val

lemma pres_isElem (N : ℕ) : IsElemPresentation (S.Gam N) (S.Kk N) (S.pres N) := by
  refine ⟨S.hdN N, ?_, ?_, ?_, ?_⟩
  · refine continuous_ofAdd.comp ?_
    exact (S.cont_X.comp continuous_subtype_val).prodMk
      (continuous_const.prodMk (continuous_const.prodMk (S.cont_del N)))
  · intro U hU
    rw [isOpen_iff_forall_mem_open]
    rintro _ ⟨z, hzU, rfl⟩
    obtain ⟨O, hO, hOU⟩ := isOpen_induced_iff.1 hU
    have hzO : (z : Multiplicative A) ∈ O := by rw [← hOU] at hzU; exact hzU
    have hpre : IsOpen ((fun x => S.emb x (S.Y z)) ⁻¹' O) :=
      hO.preimage (S.cont_emb.comp (continuous_id.prodMk continuous_const))
    have hzx : S.X z ∈ (fun x => S.emb x (S.Y z)) ⁻¹' O := by
      show S.emb (S.X z) (S.Y z) ∈ O; rw [emb_XY]; exact hzO
    refine ⟨{w | (Multiplicative.toAdd w).1 ∈ (fun x => S.emb x (S.Y z)) ⁻¹' O ∧
      (Multiplicative.toAdd w).2.2.2 = S.del N ⟨S.Y z, z.2⟩}, ?_, ?_, ?_⟩
    · rintro w ⟨hw1, hw2⟩
      have hmem : S.emb (Multiplicative.toAdd w).1 (S.Y z) ∈ S.Gam N := by
        show S.Y _ ∈ S.L N; rw [Y_emb]; exact z.2
      refine ⟨⟨_, hmem⟩, ?_, ?_⟩
      · rw [← hOU]; exact hw1
      · apply Multiplicative.toAdd.injective
        rw [pres_apply]
        refine Prod.ext ?_ (Prod.ext (Subsingleton.elim _ _) (Prod.ext (Subsingleton.elim _ _) ?_))
        · simp
        · show S.del N _ = (Multiplicative.toAdd w).2.2.2
          rw [hw2]; congr 1; apply Subtype.ext; simp
    · refine IsOpen.inter (hpre.preimage (continuous_fst.comp continuous_toAdd)) ?_
      have hc : Continuous fun w : Multiplicative (ElemGroup m 0 0 (S.sN N) (S.dN N)) =>
          (Multiplicative.toAdd w).2.2.2 :=
        continuous_snd.comp (continuous_snd.comp (continuous_snd.comp continuous_toAdd))
      exact (isOpen_discrete ({S.del N ⟨S.Y z, z.2⟩} : Set ((i : Fin (S.sN N)) → ZMod (S.dN N i)))).preimage hc
    · exact ⟨hzx, rfl⟩
  · intro w
    refine ⟨⟨S.sec N (Multiplicative.toAdd w), S.sec_mem N _⟩, ?_⟩
    apply Multiplicative.toAdd.injective
    rw [pres_sec]
  · intro z
    constructor
    · intro h
      have h1 := congrArg Multiplicative.toAdd h
      rw [pres_apply, toAdd_one] at h1
      have hx : S.X z = 0 := congrArg Prod.fst h1
      have hd : S.del N ⟨S.Y z, z.2⟩ = 0 := congrArg (fun p => p.2.2.2) h1
      exact ⟨hx, (S.del_zero_iff N _).1 hd⟩
    · rintro ⟨hx, hy⟩
      apply Multiplicative.toAdd.injective
      rw [pres_apply, toAdd_one, hx, (S.del_zero_iff N ⟨S.Y z, z.2⟩).2 hy]
      rfl

end Setup

end

end Aux_LFA

namespace Aux_LFA
open Aux_ESF

open MasulloGRH Topology Filter Set NumberField IsDedekindDomain

noncomputable section

/-! ### building the filtration from a compact open subring -/

section ringb

variable {B : Type*} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]

/-- data: a compact open subring `O` with `B = ⋃ (N!)⁻¹ O` and `⋂ N! O = 0` -/
structure RingData (B : Type*) [CommRing B] [TopologicalSpace B] where
  O : Subring B
  O_open : IsOpen (O : Set B)
  O_cpt : IsCompact (O : Set B)
  unit : ∀ N : ℕ, IsUnit ((N.factorial : ℕ) : B)
  cov : ∀ x : B, ∃ N : ℕ, ((N.factorial : ℕ) : B) * x ∈ O
  inter : ∀ x : B, (∀ N : ℕ, ∃ y ∈ O, x = ((N.factorial : ℕ) : B) * y) → x = 0

namespace RingData

variable (R : RingData B)

/-- `N!` -/
abbrev c (N : ℕ) : B := ((N.factorial : ℕ) : B)
/-- `(N!)⁻¹` -/
def ci (N : ℕ) : B := ↑((R.unit N).unit⁻¹)
lemma ci_c (N : ℕ) : R.ci N * c N = 1 := (R.unit N).val_inv_mul
lemma c_ci (N : ℕ) : c N * R.ci N = 1 := (R.unit N).mul_val_inv

/-- `L_N = (N!)⁻¹ O` -/
def L (N : ℕ) : AddSubgroup B := R.O.toAddSubgroup.comap (AddMonoidHom.mulLeft (c N))
/-- `M_N = N! O` -/
def M (N : ℕ) : AddSubgroup B := R.O.toAddSubgroup.comap (AddMonoidHom.mulLeft (R.ci N))

lemma mem_L {N x} : x ∈ R.L N ↔ c N * x ∈ R.O := Iff.rfl
lemma mem_M {N x} : x ∈ R.M N ↔ R.ci N * x ∈ R.O := Iff.rfl

lemma mem_M' {N x} : x ∈ R.M N ↔ ∃ y ∈ R.O, x = c N * y := by
  rw [mem_M]
  constructor
  · intro h; refine ⟨_, h, ?_⟩; rw [← mul_assoc, R.c_ci, one_mul]
  · rintro ⟨y, hy, rfl⟩; rwa [← mul_assoc, R.ci_c, one_mul]

lemma L_eq (N : ℕ) : (R.L N : Set B) = (fun y => R.ci N * y) '' (R.O : Set B) := by
  ext x
  constructor
  · intro h
    refine ⟨_, h, ?_⟩
    show R.ci N * (c N * x) = x
    rw [← mul_assoc, R.ci_c, one_mul]
  · rintro ⟨y, hy, rfl⟩
    show c N * (R.ci N * y) ∈ R.O
    rwa [← mul_assoc, R.c_ci, one_mul]

lemma M_eq (N : ℕ) : (R.M N : Set B) = (fun y => c N * y) '' (R.O : Set B) := by
  ext x
  rw [SetLike.mem_coe, mem_M']
  constructor
  · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩

lemma nat_mem (n : ℕ) : (n : B) ∈ R.O := natCast_mem _ n

lemma fact_dvd {N N' : ℕ} (h : N ≤ N') : ∃ t : ℕ, c N' = (t : B) * c N := by
  obtain ⟨t, ht⟩ := Nat.factorial_dvd_factorial h
  exact ⟨t, by simp only [c]; rw [ht]; push_cast; ring⟩

lemma M_inter (x : B) (hx : x ∈ ⋂ N, (R.M N : Set B)) : x = 0 :=
  R.inter x fun N => (R.mem_M').1 (mem_iInter.1 hx N)

end RingData

/-- the `Setup` attached to a `RingData` -/
def ringSetup {A : Type*} [AddCommGroup A] [TopologicalSpace A] {m : ℕ} (R : RingData B)
    (e : ((Fin m → ℝ) × B) ≃+ A) (he : Continuous e) (hes : Continuous e.symm) : Setup A B m where
  e := e
  he := he
  hes := hes
  L := R.L
  M := R.M
  L_open N := R.O_open.preimage (continuous_mul_left (RingData.c N : B))
  L_cpt N := by rw [R.L_eq]; exact R.O_cpt.image (continuous_mul_left (R.ci N))
  M_open N := R.O_open.preimage (continuous_mul_left (R.ci N))
  M_cpt N := by rw [R.M_eq]; exact R.O_cpt.image (continuous_mul_left (RingData.c N : B))
  L_mono N N' h x hx := by
    obtain ⟨t, ht⟩ := RingData.fact_dvd (B := B) h
    show RingData.c N' * x ∈ R.O
    rw [ht, mul_assoc]; exact mul_mem (R.nat_mem t) hx
  M_anti N N' h x hx := by
    obtain ⟨y, hy, rfl⟩ := (R.mem_M').1 hx
    obtain ⟨t, ht⟩ := RingData.fact_dvd (B := B) h
    refine (R.mem_M').2 ⟨t * y, mul_mem (R.nat_mem t) hy, ?_⟩
    rw [ht]; ring
  ML N x hx := by
    obtain ⟨y, hy, rfl⟩ := (R.mem_M').1 hx
    show RingData.c N * (RingData.c N * y) ∈ R.O
    exact mul_mem (R.nat_mem _) (mul_mem (R.nat_mem _) hy)
  L_cov x := R.cov x
  M_small W hW := by
    have hdir : Directed (· ⊇ ·) (fun N => (R.M N : Set B)) := by
      intro a b
      refine ⟨max a b, ?_, ?_⟩
      · intro x hx
        obtain ⟨y, hy, rfl⟩ := (R.mem_M').1 hx
        obtain ⟨t, ht⟩ := RingData.fact_dvd (B := B) (le_max_left a b)
        exact (R.mem_M').2 ⟨t * y, mul_mem (R.nat_mem t) hy, by rw [ht]; ring⟩
      · intro x hx
        obtain ⟨y, hy, rfl⟩ := (R.mem_M').1 hx
        obtain ⟨t, ht⟩ := RingData.fact_dvd (B := B) (le_max_right a b)
        exact (R.mem_M').2 ⟨t * y, mul_mem (R.nat_mem t) hy, by rw [ht]; ring⟩
    exact exists_subset_nhds_of_isCompact' hdir
      (fun N => by rw [R.M_eq]; exact R.O_cpt.image (continuous_mul_left (RingData.c N : B)))
      (fun N => AddSubgroup.isClosed_of_isOpen _ (R.O_open.preimage (continuous_mul_left (R.ci N))))
      (fun x hx => by rw [R.M_inter x hx]; exact hW)

end ringb

/-! ### the local fields -/

section local_

open IsLocalRing
open scoped WithZero

variable {F : Type*} [Field F] [NumberField F]

theorem nonempty_residueFieldEquiv (v : HeightOneSpectrum (𝓞 F)) :
    Nonempty ((𝓞 F ⧸ v.asIdeal) ≃+* IsLocalRing.ResidueField (v.adicCompletionIntegers F)) := by
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
    Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) := by
  obtain ⟨e⟩ := nonempty_residueFieldEquiv v
  have : Finite (𝓞 F ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  exact Finite.of_equiv _ e.toEquiv

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

lemma natc (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) :
    ((n : ℕ) : v.adicCompletion F) = (((n : ℕ) : F) : v.adicCompletion F) := by
  induction n with
  | zero => rw [Nat.cast_zero, Nat.cast_zero, HeightOneSpectrum.adicCompletion.coe_zero]
  | succ n ih => rw [Nat.cast_succ, Nat.cast_succ, ih, HeightOneSpectrum.adicCompletion.coe_add, HeightOneSpectrum.adicCompletion.coe_one]

lemma norm_nat_le (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) : ‖((n : ℕ) : v.adicCompletion F)‖ ≤ 1 := by
  refine (Valued.toNormedField.norm_le_one_iff).2 ?_
  rw [natc, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  have := v.valuation_le_one (K := F) (n : 𝓞 F)
  simpa using this

lemma norm_absNorm_lt (v : HeightOneSpectrum (𝓞 F)) :
    ‖((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F)‖ < 1 := by
  refine (Valued.toNormedField.norm_lt_one_iff).2 ?_
  rw [natc, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  have := (v.valuation_lt_one_iff_mem (K := F) ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F)).2
    (Ideal.absNorm_mem v.asIdeal)
  simpa using this

lemma fact_small (v : HeightOneSpectrum (𝓞 F)) (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N ≥ N0, ‖((N.factorial : ℕ) : v.adicCompletion F)‖ < ε := by
  set nn := Ideal.absNorm v.asIdeal
  have hq := norm_absNorm_lt v
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε hq
  have hnn : nn ≠ 0 := by
    intro h; exact v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  refine ⟨nn ^ k, fun N hN => ?_⟩
  obtain ⟨t, ht⟩ := Nat.dvd_factorial (pow_pos (Nat.pos_of_ne_zero hnn) k) hN
  rw [ht]
  push_cast
  rw [norm_mul, norm_pow]
  calc ‖(nn : v.adicCompletion F)‖ ^ k * ‖(t : v.adicCompletion F)‖
      ≤ ‖(nn : v.adicCompletion F)‖ ^ k * 1 :=
        mul_le_mul_of_nonneg_left (norm_nat_le v t) (by positivity)
    _ < ε := by rw [mul_one]; exact hk

lemma mem_O_iff (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) :
    x ∈ v.adicCompletionIntegers F ↔ ‖x‖ ≤ 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  exact (Valued.toNormedField.norm_le_one_iff).symm

lemma loc_cov (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) :
    ∃ N0 : ℕ, ∀ N ≥ N0, ((N.factorial : ℕ) : v.adicCompletion F) * x ∈ v.adicCompletionIntegers F := by
  by_cases hx : x = 0
  · exact ⟨0, fun N _ => by rw [hx, mul_zero]; exact zero_mem _⟩
  have hpos : 0 < ‖x‖ := norm_pos_iff.2 hx
  obtain ⟨N0, hN0⟩ := fact_small v (1 / ‖x‖) (by positivity)
  refine ⟨N0, fun N hN => (mem_O_iff v _).2 ?_⟩
  rw [norm_mul]
  have := hN0 N hN
  rw [lt_div_iff₀ hpos] at this
  exact this.le

lemma loc_inter (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F)
    (h : ∀ N : ℕ, ∃ y ∈ v.adicCompletionIntegers F, x = ((N.factorial : ℕ) : v.adicCompletion F) * y) :
    x = 0 := by
  by_contra hx
  have hpos : 0 < ‖x‖ := norm_pos_iff.2 hx
  obtain ⟨N0, hN0⟩ := fact_small v ‖x‖ hpos
  obtain ⟨y, hy, hxy⟩ := h N0
  have h1 := hN0 N0 le_rfl
  have h2 : ‖x‖ ≤ ‖((N0.factorial : ℕ) : v.adicCompletion F)‖ := by
    rw [hxy, norm_mul]
    calc _ ≤ ‖((N0.factorial : ℕ) : v.adicCompletion F)‖ * 1 :=
          mul_le_mul_of_nonneg_left ((mem_O_iff v y).1 hy) (norm_nonneg _)
      _ = _ := mul_one _
  linarith

end local_

end

end Aux_LFA

namespace Aux_LFA
open Aux_ESF

open MasulloGRH Topology Filter Set NumberField IsDedekindDomain

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

lemma fact_ne (N : ℕ) : ((N.factorial : ℕ) : F) ≠ 0 :=
  Nat.cast_ne_zero.2 (Nat.factorial_ne_zero N)

/-! ### the finite adeles -/

lemma fin_nat_apply (n : ℕ) (v : HeightOneSpectrum (𝓞 F)) :
    ((n : ℕ) : FiniteAdeleRing (𝓞 F) F) v = ((n : ℕ) : v.adicCompletion F) := by
  rw [← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)), FiniteAdeleRing.algebraMap_apply,
    natc]

/-- the integral finite adeles -/
def finO : Subring (FiniteAdeleRing (𝓞 F) F) where
  carrier := {x | ∀ v, x v ∈ v.adicCompletionIntegers F}
  mul_mem' {x y} hx hy v := by
    show x v * y v ∈ _
    exact mul_mem (hx v) (hy v)
  one_mem' v := by
    show (1 : v.adicCompletion F) ∈ _
    exact one_mem _
  add_mem' {x y} hx hy v := by
    show x v + y v ∈ _
    exact add_mem (hx v) (hy v)
  zero_mem' v := by
    show (0 : v.adicCompletion F) ∈ _
    exact zero_mem _
  neg_mem' {x} hx v := by
    show -x v ∈ _
    exact neg_mem (hx v)

lemma finO_open : IsOpen (finO F : Set (FiniteAdeleRing (𝓞 F) F)) :=
  RestrictedProduct.isOpen_forall_mem (fun v => isOpen_adicCompletionIntegers v)

lemma finO_cpt : IsCompact (finO F : Set (FiniteAdeleRing (𝓞 F) F)) := by
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), CompactSpace (v.adicCompletionIntegers F) :=
    fun v => compactSpace_adicCompletionIntegers v
  have h := isCompact_range (RestrictedProduct.isEmbedding_structureMap (R := fun v :
    HeightOneSpectrum (𝓞 F) => v.adicCompletion F) (A := fun v => (v.adicCompletionIntegers F :
    Set (v.adicCompletion F))) (𝓕 := Filter.cofinite)).continuous
  rw [RestrictedProduct.range_structureMap] at h
  exact h

/-- the ring data of the finite adeles -/
def finRD : RingData (FiniteAdeleRing (𝓞 F) F) where
  O := finO F
  O_open := finO_open F
  O_cpt := finO_cpt F
  unit N := by
    rw [← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F))]
    exact (Ne.isUnit (fact_ne F N)).map _
  cov x := by
    classical
    have hfin : {v : HeightOneSpectrum (𝓞 F) | ¬ x v ∈ v.adicCompletionIntegers F}.Finite :=
      Filter.eventually_cofinite.1 x.2
    choose Nv hNv using fun v : HeightOneSpectrum (𝓞 F) => loc_cov v (x v)
    refine ⟨hfin.toFinset.sup Nv, fun v => ?_⟩
    show ((((hfin.toFinset.sup Nv).factorial : ℕ) : FiniteAdeleRing (𝓞 F) F) v) * x v ∈ _
    rw [fin_nat_apply]
    by_cases hv : x v ∈ v.adicCompletionIntegers F
    · exact mul_mem (natCast_mem _ _) hv
    · exact hNv v _ (Finset.le_sup (f := Nv) (hfin.mem_toFinset.2 hv))
  inter x hx := by
    refine FiniteAdeleRing.ext F fun v => ?_
    refine (loc_inter v (x v) fun N => ?_).trans rfl
    obtain ⟨y, hy, rfl⟩ := hx N
    refine ⟨y v, hy v, ?_⟩
    show ((((N.factorial : ℕ) : FiniteAdeleRing (𝓞 F) F)) v) * y v = _
    rw [fin_nat_apply]

/-! ### the finite part of the `S`-adeles -/

/-! ### the infinite adeles as a real vector space -/

lemma cont_mixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  have : ⇑(InfiniteAdeleRing.ringEquiv_mixedSpace F) = fun x =>
      ((fun (v : {w : InfinitePlace F // InfinitePlace.IsReal w}) =>
        InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
       (fun (v : {w : InfinitePlace F // InfinitePlace.IsComplex w}) =>
        InfinitePlace.Completion.extensionEmbedding v.1 (x v))) :=
    funext (InfiniteAdeleRing.ringEquiv_mixedSpace_apply F)
  rw [this]
  refine (continuous_pi fun v => ?_).prodMk (continuous_pi fun v => ?_)
  · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp
      (continuous_apply _)
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp
      (continuous_apply _)

lemma cont_mixed_symm : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by
  set g := (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
  have hg : ∀ y, InfiniteAdeleRing.ringEquiv_mixedSpace F (g y) = y := fun y =>
    RingEquiv.apply_symm_apply _ y
  refine continuous_pi fun w => ?_
  by_cases hw : InfinitePlace.IsReal w
  · have hi := (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).isUniformInducing.isInducing
    refine hi.continuous_iff.2 ?_
    have : (⇑(InfinitePlace.Completion.extensionEmbeddingOfIsReal hw) ∘ fun y => g y w) =
        fun y => y.1 ⟨w, hw⟩ := by
      funext y
      have := congrArg (fun p => p.1 ⟨w, hw⟩) (hg y)
      simpa using this
    rw [this]; exact (continuous_apply _).comp continuous_fst
  · have hc : InfinitePlace.IsComplex w := InfinitePlace.not_isReal_iff_isComplex.1 hw
    have hi := (InfinitePlace.Completion.isometry_extensionEmbedding w).isUniformInducing.isInducing
    refine hi.continuous_iff.2 ?_
    have : (⇑(InfinitePlace.Completion.extensionEmbedding w) ∘ fun y => g y w) =
        fun y => y.2 ⟨w, hc⟩ := by
      funext y
      have := congrArg (fun p => p.2 ⟨w, hc⟩) (hg y)
      simpa using this
    rw [this]; exact (continuous_apply _).comp continuous_snd

/-- the real dimension -/
abbrev dimV : ℕ := Module.finrank ℝ (mixedEmbedding.mixedSpace F)

/-- `mixedSpace ≅ ℝ^d` -/
def linV : mixedEmbedding.mixedSpace F ≃ₗ[ℝ] (Fin (dimV F) → ℝ) :=
  LinearEquiv.ofFinrankEq _ _ (by simp)

/-- `K_∞ ≅ ℝ^d` -/
def eV : InfiniteAdeleRing F ≃+ (Fin (dimV F) → ℝ) :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toAddEquiv.trans (linV F).toAddEquiv

lemma cont_eV : Continuous (eV F) :=
  (LinearMap.continuous_of_finiteDimensional (linV F).toLinearMap).comp (cont_mixed F)

lemma cont_eV_symm : Continuous (eV F).symm :=
  (cont_mixed_symm F).comp (LinearMap.continuous_of_finiteDimensional (linV F).symm.toLinearMap)

/-- `ℝ^0 × B ≅ B` -/
def e0 (B : Type*) [AddCommGroup B] : ((Fin 0 → ℝ) × B) ≃+ B where
  toFun p := p.2
  invFun y := (0, y)
  left_inv p := Prod.ext (Subsingleton.elim _ _) rfl
  right_inv y := rfl
  map_add' _ _ := rfl

end

end Aux_LFA


namespace Aux_GZ

open MasulloGRH NumberField IsDedekindDomain Filter Topology
open Aux_MasulloGRH_idele_class_group_topology
open scoped WithZero

noncomputable section

local notation "AQ" => AdeleRing (𝓞 ℚ) ℚ
local notation "IQ" => IdeleGroup ℚ

lemma isReal_w (w : InfinitePlace ℚ) : w.IsReal := by
  rw [Subsingleton.elim w Rat.infinitePlace]; exact Rat.isReal_infinitePlace

/-- the real embedding at an infinite place of `ℚ` -/
def ιr (w : InfinitePlace ℚ) : w.Completion ≃+* ℝ :=
  InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_w w)

lemma ιr_norm (w : InfinitePlace ℚ) (x : w.Completion) : ‖x‖ = |ιr w x| := by
  have := (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal
    (isReal_w w)).norm_map_of_map_zero (map_zero _) x
  rw [← Real.norm_eq_abs]; exact this.symm

lemma ιr_cont (w : InfinitePlace ℚ) : Continuous (ιr w) :=
  (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal (isReal_w w)).continuous

lemma ιr_symm_cont (w : InfinitePlace ℚ) : Continuous (ιr w).symm :=
  (InfinitePlace.Completion.isometryEquivRealOfIsReal (isReal_w w)).symm.isometry.continuous

lemma ιr_rat (w : InfinitePlace ℚ) (q : ℚ) : ιr w (algebraMap ℚ w.Completion q) = q :=
  eq_ratCast ((ιr w).toRingHom.comp (algebraMap ℚ w.Completion)) q

/-- the infinite place -/
abbrev w0 : InfinitePlace ℚ := Rat.infinitePlace

/-- the infinite coordinate of an idele, as a real number -/
def inf (g : IQ) : ℝ := ιr w0 ((g : AQ).1 w0)

lemma inf_mul (g h : IQ) : inf (g * h) = inf g * inf h := by
  unfold inf; rw [← map_mul]; rfl

lemma inf_one : inf 1 = 1 := by unfold inf; rw [← map_one (ιr w0)]; rfl

lemma inf_principal (ξ : ℚˣ) (g : IQ) : inf (principalIdele ℚ ξ * g) = ((ξ : ℚ) : ℝ) * inf g := by
  rw [inf_mul]; congr 1; exact ιr_rat w0 ξ

lemma inf_cont : Continuous inf :=
  (ιr_cont w0).comp ((continuous_apply w0).comp (continuous_fst.comp Units.continuous_val))

lemma inf_inv (g : IQ) : inf g⁻¹ * inf g = 1 := by rw [← inf_mul, inv_mul_cancel, inf_one]

lemma prod_inf (g : IQ) : (∏ w : InfinitePlace ℚ, ‖(g : AQ).1 w‖ ^ w.mult) = |inf g| := by
  rw [Fintype.prod_unique]
  have hd : (default : InfinitePlace ℚ) = w0 := Subsingleton.elim _ _
  rw [hd]
  have hm : w0.mult = 1 := by simp [InfinitePlace.mult, Rat.isReal_infinitePlace]
  rw [hm, pow_one, ιr_norm]; rfl

lemma v_mul_inv (g : IQ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    Valued.v ((g : AQ).2 v) * Valued.v (((g⁻¹ : IQ) : AQ).2 v) = 1 := by
  rw [← map_mul, fin_mul_inv, map_one]

lemma at_iff (g : IQ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    Valued.v ((g : AQ).2 v) = 1 ↔ ((g : AQ).2 v ∈ v.adicCompletionIntegers ℚ ∧
      ((g⁻¹ : IQ) : AQ).2 v ∈ v.adicCompletionIntegers ℚ) := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.mem_adicCompletionIntegers]
  have h3 := v_mul_inv g v
  constructor
  · intro h1
    rw [h1, one_mul] at h3
    exact ⟨h1.le, h3.le⟩
  · rintro ⟨h1, h2⟩
    refine le_antisymm h1 (not_lt.1 fun hlt => ?_)
    have : Valued.v ((g : AQ).2 v) * Valued.v (((g⁻¹ : IQ) : AQ).2 v) < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_right' h2) hlt
    rw [h3] at this; exact lt_irrefl _ this

/-- integral units at every finite place -/
def IU (g : IQ) : Prop := ∀ v : HeightOneSpectrum (𝓞 ℚ), Valued.v ((g : AQ).2 v) = 1

/-- the subgroup `ℝ_{>0} × \hat ℤ^×` -/
def Up : Set IQ := {g | 0 < inf g ∧ IU g}

lemma IU_mul {g h : IQ} (hg : IU g) (hh : IU h) : IU (g * h) := fun v => by
  show Valued.v ((g : AQ).2 v * (h : AQ).2 v) = 1
  rw [map_mul, hg v, hh v, one_mul]

lemma IU_inv {g : IQ} (hg : IU g) : IU g⁻¹ := fun v => by
  have := v_mul_inv g v; rw [hg v, one_mul] at this; exact this

lemma Up_mul {g h : IQ} (hg : g ∈ Up) (hh : h ∈ Up) : g * h ∈ Up :=
  ⟨by rw [inf_mul]; exact mul_pos hg.1 hh.1, IU_mul hg.2 hh.2⟩

lemma Up_inv {g : IQ} (hg : g ∈ Up) : g⁻¹ ∈ Up := by
  refine ⟨?_, IU_inv hg.2⟩
  have h := inf_inv g
  by_contra hc
  push_neg at hc
  have : inf g⁻¹ * inf g ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc hg.1.le
  linarith

lemma one_Up : (1 : IQ) ∈ Up :=
  ⟨by rw [inf_one]; exact one_pos, fun v => by show Valued.v (1 : v.adicCompletion ℚ) = 1; exact map_one _⟩

lemma isOpen_Up : IsOpen Up := by
  have h1 : IsOpen {g : IQ | 0 < inf g} := isOpen_lt continuous_const inf_cont
  convert h1.inter (isOpen_integralUnits (F := ℚ)) using 1
  ext g
  simp only [Up, IU, Set.mem_setOf_eq, Set.mem_inter_iff]
  exact and_congr Iff.rfl (forall_congr' fun v => at_iff g v)

lemma ideleNorm_Up {g : IQ} (hg : IU g) : ideleNorm g = |inf g| := by
  rw [ideleNorm_eq_infNorm g fun v => (at_iff g v).1 (hg v), prod_inf]

lemma val_principal (ξ : ℚˣ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    Valued.v (((principalIdele ℚ ξ : IQ) : AQ).2 v) = v.valuation ℚ (ξ : ℚ) := by
  show Valued.v ((algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ : ℚ)) v) = _
  rw [FiniteAdeleRing.algebraMap_apply]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (ξ : ℚ)

lemma int_of_val (q : ℚ) (h : ∀ v : HeightOneSpectrum (𝓞 ℚ), v.valuation ℚ q ≤ 1) :
    ∃ n : ℤ, (n : ℚ) = q := by
  obtain ⟨a, rfl⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 ℚ) (K := ℚ) q h
  obtain ⟨n, rfl⟩ := Rat.int_algebraMap_surjective (𝓞 ℚ) a
  exact ⟨n, by simp⟩

lemma uq (ξ : ℚˣ) (h : principalIdele ℚ ξ ∈ Up) : ξ = 1 := by
  obtain ⟨hpos, hI⟩ := h
  have h1 : ∀ v : HeightOneSpectrum (𝓞 ℚ), v.valuation ℚ (ξ : ℚ) = 1 := fun v => by
    rw [← val_principal]; exact hI v
  obtain ⟨n, hn⟩ := int_of_val (ξ : ℚ) fun v => (h1 v).le
  obtain ⟨m, hm⟩ := int_of_val ((ξ : ℚ)⁻¹) fun v => by rw [map_inv₀, h1 v, inv_one]
  have hnm : n * m = 1 := by
    have : ((n * m : ℤ) : ℚ) = 1 := by push_cast; rw [hn, hm, mul_inv_cancel₀ ξ.ne_zero]
    exact_mod_cast this
  have hpos' : (0 : ℝ) < ((ξ : ℚ) : ℝ) := by
    have := inf_principal ξ 1; rw [mul_one, inf_one, mul_one] at this; rw [← this]; exact hpos
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hnm with h | h
  · ext; rw [← hn, h]; simp
  · exfalso; rw [← hn, h] at hpos'; norm_num at hpos'

/-- uniqueness of the decomposition -/
lemma uq2 {ξ η : ℚˣ} {g : IQ} (h1 : principalIdele ℚ ξ * g ∈ Up) (h2 : principalIdele ℚ η * g ∈ Up) :
    ξ = η := by
  have : principalIdele ℚ (ξ * η⁻¹) = (principalIdele ℚ ξ * g) * (principalIdele ℚ η * g)⁻¹ := by
    rw [map_mul, map_inv]; group
  have h := uq _ (this ▸ Up_mul h1 (Up_inv h2))
  exact mul_inv_eq_one.1 h

end

end Aux_GZ


namespace Aux_GZ

open MasulloGRH NumberField IsDedekindDomain Filter Topology
open Aux_MasulloGRH_idele_class_group_topology
open scoped WithZero

noncomputable section

local notation "AQ" => AdeleRing (𝓞 ℚ) ℚ
local notation "IQ" => IdeleGroup ℚ

instance pidQ : IsPrincipalIdealRing (𝓞 ℚ) :=
  IsPrincipalIdealRing.of_surjective Rat.ringOfIntegersEquiv.symm
    Rat.ringOfIntegersEquiv.symm.surjective

/-- a generator of the prime of `v` -/
def rv (v : HeightOneSpectrum (𝓞 ℚ)) : 𝓞 ℚ := Submodule.IsPrincipal.generator v.asIdeal

lemma rv_span (v : HeightOneSpectrum (𝓞 ℚ)) : v.asIdeal = Ideal.span {rv v} :=
  (Ideal.span_singleton_generator v.asIdeal).symm

lemma rv_ne (v : HeightOneSpectrum (𝓞 ℚ)) : rv v ≠ 0 := fun h =>
  v.ne_bot (by rw [rv_span, h, Ideal.span_singleton_eq_bot.2 rfl])

lemma rv_val_self (v : HeightOneSpectrum (𝓞 ℚ)) :
    v.valuation ℚ (algebraMap (𝓞 ℚ) ℚ (rv v)) = WithZero.exp (-1 : ℤ) := by
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  exact v.intValuation_singleton (rv_ne v) (rv_span v)

lemma rv_val_other {v w : HeightOneSpectrum (𝓞 ℚ)} (hvw : w ≠ v) :
    w.valuation ℚ (algebraMap (𝓞 ℚ) ℚ (rv v)) = 1 := by
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
  intro hmem
  apply hvw
  have hle : v.asIdeal ≤ w.asIdeal := by
    rw [rv_span v, Ideal.span_le, Set.singleton_subset_iff]; exact hmem
  have := v.isMaximal.eq_of_le w.isPrime.ne_top hle
  exact (HeightOneSpectrum.ext this).symm

/-- the uniformizer as a unit of `ℚ` -/
def uv (v : HeightOneSpectrum (𝓞 ℚ)) : ℚˣ :=
  Units.mk0 (algebraMap (𝓞 ℚ) ℚ (rv v))
    ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 ℚ) ℚ)).2 (rv_ne v))

lemma val_comp (ξ : ℚˣ) (g : IQ) (w : HeightOneSpectrum (𝓞 ℚ)) :
    Valued.v (((principalIdele ℚ ξ * g : IQ) : AQ).2 w) =
      w.valuation ℚ (ξ : ℚ) * Valued.v ((g : AQ).2 w) := by
  rw [← val_principal]
  show Valued.v (((principalIdele ℚ ξ : IQ) : AQ).2 w * (g : AQ).2 w) = _
  rw [map_mul]

lemma val_ne_zero (g : IQ) (v : HeightOneSpectrum (𝓞 ℚ)) : Valued.v ((g : AQ).2 v) ≠ 0 := by
  intro h; have := v_mul_inv g v; rw [h, zero_mul] at this; exact zero_ne_one this

lemma fix_at (g : IQ) (v : HeightOneSpectrum (𝓞 ℚ)) : ∃ k : ℤ,
    Valued.v (((principalIdele ℚ (uv v ^ k) * g : IQ) : AQ).2 v) = 1 ∧
    ∀ w, w ≠ v → Valued.v (((principalIdele ℚ (uv v ^ k) * g : IQ) : AQ).2 w) =
      Valued.v ((g : AQ).2 w) := by
  have hL : Valued.v ((g : AQ).2 v) = WithZero.exp (WithZero.log (Valued.v ((g : AQ).2 v))) :=
    (WithZero.exp_log (val_ne_zero g v)).symm
  set L := WithZero.log (Valued.v ((g : AQ).2 v))
  refine ⟨L, ?_, ?_⟩
  · rw [val_comp, Units.val_zpow_eq_zpow_val, map_zpow₀]
    show v.valuation ℚ (algebraMap (𝓞 ℚ) ℚ (rv v)) ^ _ * _ = 1
    rw [rv_val_self, ← WithZero.exp_zsmul, hL]
    rw [← WithZero.exp_add, smul_neg, smul_eq_mul, mul_one, neg_add_cancel, WithZero.exp_zero]
  · intro w hw
    rw [val_comp, Units.val_zpow_eq_zpow_val, map_zpow₀]
    show w.valuation ℚ (algebraMap (𝓞 ℚ) ℚ (rv v)) ^ _ * _ = _
    rw [rv_val_other hw, one_zpow, one_mul]

/-- the bad places -/
def bad (g : IQ) : Set (HeightOneSpectrum (𝓞 ℚ)) := {v | Valued.v ((g : AQ).2 v) ≠ 1}

lemma bad_finite (g : IQ) : (bad g).Finite := by
  have h1 := Filter.eventually_cofinite.1 (g : AQ).2.2
  have h2 := Filter.eventually_cofinite.1 ((g⁻¹ : IQ) : AQ).2.2
  refine (h1.union h2).subset fun v hv => ?_
  by_contra hc
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc
  exact hv ((at_iff g v).2 hc)

lemma dec_IU_aux (s : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    ∀ g : IQ, bad g ⊆ s → ∃ ξ : ℚˣ, IU (principalIdele ℚ ξ * g) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro g hg
    refine ⟨1, fun v => ?_⟩
    rw [map_one, one_mul]
    by_contra hc
    exact absurd (hg hc) (by simp)
  | insert v s hv ih =>
    intro g hg
    obtain ⟨k, hk1, hk2⟩ := fix_at g v
    obtain ⟨ξ, hξ⟩ := ih (principalIdele ℚ (uv v ^ k) * g) (by
      intro w hw
      have hwv : w ≠ v := by rintro rfl; exact hw hk1
      have : w ∈ bad g := by
        show Valued.v ((g : AQ).2 w) ≠ 1
        rw [← hk2 w hwv]; exact hw
      have := hg this
      rw [Finset.coe_insert] at this
      exact (Set.mem_insert_iff.1 this).resolve_left hwv)
    refine ⟨ξ * uv v ^ k, ?_⟩
    rw [map_mul, mul_assoc]; exact hξ

lemma dec_IU (g : IQ) : ∃ ξ : ℚˣ, IU (principalIdele ℚ ξ * g) :=
  dec_IU_aux (bad_finite g).toFinset g (by rw [Set.Finite.coe_toFinset])

lemma inf_ne_zero (g : IQ) : inf g ≠ 0 := by
  intro h; have := inf_inv g; rw [h, mul_zero] at this; exact zero_ne_one this

lemma val_neg_one (v : HeightOneSpectrum (𝓞 ℚ)) : v.valuation ℚ ((-1 : ℚˣ) : ℚ) = 1 := by
  rw [Units.val_neg, Units.val_one, Valuation.map_neg, map_one]

lemma dec (g : IQ) : ∃ ξ : ℚˣ, principalIdele ℚ ξ * g ∈ Up := by
  obtain ⟨ξ, hξ⟩ := dec_IU g
  rcases lt_or_gt_of_ne (inf_ne_zero (principalIdele ℚ ξ * g)) with h | h
  · refine ⟨-1 * ξ, ?_, ?_⟩
    · rw [map_mul, mul_assoc, inf_principal]; push_cast; linarith
    · intro v; rw [map_mul, mul_assoc, val_comp, val_neg_one, one_mul]; exact hξ v
  · exact ⟨ξ, h, hξ⟩

end

end Aux_GZ


namespace Aux_GZ

open MasulloGRH NumberField IsDedekindDomain Filter Topology
open Aux_MasulloGRH_idele_class_group_topology
open scoped WithZero

noncomputable section

local notation "AQ" => AdeleRing (𝓞 ℚ) ℚ
local notation "IQ" => IdeleGroup ℚ

/-- the prime `3` -/
def p3 : Nat.Primes := ⟨3, Nat.prime_three⟩


/-- the place `3` -/
def v3 : HeightOneSpectrum (𝓞 ℚ) := Rat.HeightOneSpectrum.primesEquiv.symm p3

/-- `𝒪_{v_3} ≅ ℤ_3` -/
def E3 : v3.adicCompletionIntegers ℚ ≃A[ℤ] ℤ_[3] :=
  (PadicInt.adicCompletionIntegersEquiv (𝓞 ℚ) p3).symm

open Classical in
/-- reduction mod `3` of the `3`-adic coordinate -/
def z (g : IQ) : ZMod 3 :=
  if hm : (g : AQ).2 v3 ∈ v3.adicCompletionIntegers ℚ then PadicInt.toZMod (E3 ⟨_, hm⟩) else 0

lemma z_mul {g h : IQ} (hg : (g : AQ).2 v3 ∈ v3.adicCompletionIntegers ℚ)
    (hh : (h : AQ).2 v3 ∈ v3.adicCompletionIntegers ℚ) : z (g * h) = z g * z h := by
  have hgh : ((g * h : IQ) : AQ).2 v3 ∈ v3.adicCompletionIntegers ℚ := mul_mem hg hh
  unfold z
  rw [dif_pos hg, dif_pos hh, dif_pos hgh, ← map_mul, ← map_mul]
  rfl

lemma z_one : z 1 = 1 := by
  have h1 : ((1 : IQ) : AQ).2 v3 ∈ v3.adicCompletionIntegers ℚ := one_mem _
  unfold z
  rw [dif_pos h1]
  have : (⟨((1 : IQ) : AQ).2 v3, h1⟩ : v3.adicCompletionIntegers ℚ) = 1 := rfl
  rw [this, map_one, map_one]

lemma mem3 {g : IQ} (hg : IU g) : (g : AQ).2 v3 ∈ v3.adicCompletionIntegers ℚ :=
  ((at_iff g v3).1 (hg v3)).1

lemma z_ne {g : IQ} (hg : IU g) : z g ≠ 0 := by
  intro h0
  have := z_mul (mem3 hg) (mem3 (IU_inv hg))
  rw [mul_inv_cancel, z_one, h0, zero_mul] at this
  exact zero_ne_one this.symm

/-- the mod-3 character on `ℝ_{>0} × \hat ℤ^×` -/
def χ (g : IQ) : ℂ := if z g = 1 then 1 else -1

lemma zmod3 : ∀ a b : ZMod 3, a ≠ 0 → b ≠ 0 → (a * b = 1 ↔ (a = 1 ↔ b = 1)) := by decide

lemma χ_mul {g h : IQ} (hg : IU g) (hh : IU h) : χ (g * h) = χ g * χ h := by
  have e := zmod3 (z g) (z h) (z_ne hg) (z_ne hh)
  unfold χ
  rw [z_mul (mem3 hg) (mem3 hh)]
  by_cases h1 : z g = 1 <;> by_cases h2 : z h = 1 <;> simp_all

lemma χ_one : χ 1 = 1 := by unfold χ; rw [if_pos z_one]

lemma χ_norm (g : IQ) : ‖χ g‖ = 1 := by unfold χ; split_ifs <;> simp

lemma χ_ne (g : IQ) : χ g ≠ 0 := by unfold χ; split_ifs <;> simp

lemma eval3_cont : Continuous (fun g : IQ => (g : AQ).2 v3) :=
  (RestrictedProduct.continuous_eval v3).comp (continuous_snd.comp Units.continuous_val)

/-- the open set on which the character is `1` -/
def W : Set IQ := {g | g ∈ Up ∧ ‖(g : AQ).2 v3 - 1‖ < 1}

lemma isOpen_W : IsOpen W :=
  isOpen_Up.inter (isOpen_lt (continuous_norm.comp (eval3_cont.sub continuous_const))
    continuous_const)

lemma one_W : (1 : IQ) ∈ W := ⟨one_Up, by
  show ‖(1 : v3.adicCompletion ℚ) - 1‖ < 1
  rw [sub_self, norm_zero]; exact one_pos⟩

lemma χ_W {g : IQ} (hg : g ∈ W) : χ g = 1 := by
  obtain ⟨hU, hn⟩ := hg
  have hv : Valued.v ((g : AQ).2 v3 - 1) < 1 := Valued.toNormedField.norm_lt_one_iff.1 hn
  have hm : (g : AQ).2 v3 - 1 ∈ v3.adicCompletionIntegers ℚ :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hv.le
  set x : v3.adicCompletionIntegers ℚ := ⟨_, hm⟩
  have hnu : ¬ IsUnit (E3 x) := by
    intro hu
    have hx : IsUnit x := by
      have := hu.map E3.symm
      rwa [ContinuousAlgEquiv.symm_apply_apply] at this
    obtain ⟨y, hy⟩ := hx.exists_right_inv
    have h1 : Valued.v (x : v3.adicCompletion ℚ) * Valued.v (y : v3.adicCompletion ℚ) = 1 := by
      rw [← map_mul]
      have : ((x * y : v3.adicCompletionIntegers ℚ) : v3.adicCompletion ℚ) = 1 := by rw [hy]; rfl
      rw [show ((x : v3.adicCompletion ℚ) * y) = 1 from this, map_one]
    have h2 : Valued.v (y : v3.adicCompletion ℚ) ≤ 1 :=
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 y.2
    have : Valued.v (x : v3.adicCompletion ℚ) * Valued.v (y : v3.adicCompletion ℚ) < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_right' h2) hv
    rw [h1] at this; exact lt_irrefl _ this
  have h0 : PadicInt.toZMod (E3 x) = 0 := by
    rw [← RingHom.mem_ker, PadicInt.ker_toZMod]
    exact (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 hnu)
  have hg3 := mem3 hU.2
  have hxe : (⟨(g : AQ).2 v3, hg3⟩ : v3.adicCompletionIntegers ℚ) = x + 1 := by
    apply Subtype.ext; simp [x]
  unfold χ z
  rw [dif_pos hg3, hxe, map_add, map_add, h0, map_one, map_one, zero_add, if_pos rfl]

/-- the idele class character of conductor `3` -/
def c0 (g : IQ) : ℂ := χ (principalIdele ℚ (Classical.choose (dec g)) * g)

lemma c0_eq {ξ : ℚˣ} {g : IQ} (h : principalIdele ℚ ξ * g ∈ Up) :
    c0 g = χ (principalIdele ℚ ξ * g) := by
  unfold c0
  rw [uq2 (Classical.choose_spec (dec g)) h]

lemma c0_mul (g h : IQ) : c0 (g * h) = c0 g * c0 h := by
  have hg := Classical.choose_spec (dec g)
  have hh := Classical.choose_spec (dec h)
  set ξ := Classical.choose (dec g)
  set η := Classical.choose (dec h)
  have e : principalIdele ℚ (ξ * η) * (g * h) =
      (principalIdele ℚ ξ * g) * (principalIdele ℚ η * h) := by
    rw [map_mul]; exact mul_mul_mul_comm _ _ _ _
  have hU : principalIdele ℚ (ξ * η) * (g * h) ∈ Up := by rw [e]; exact Up_mul hg hh
  rw [c0_eq hU, e, χ_mul hg.2 hh.2, c0_eq hg, c0_eq hh]

lemma c0_principal (η : ℚˣ) : c0 (principalIdele ℚ η) = 1 := by
  have e : principalIdele ℚ η⁻¹ * principalIdele ℚ η = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have hU : principalIdele ℚ η⁻¹ * principalIdele ℚ η ∈ Up := by rw [e]; exact one_Up
  rw [c0_eq hU, e, χ_one]

lemma c0_cont : Continuous c0 := by
  refine continuous_iff_continuousAt.2 fun g => ?_
  have hW : {h : IQ | g⁻¹ * h ∈ W} ∈ 𝓝 g := by
    have : ContinuousAt (fun h : IQ => g⁻¹ * h) g := (continuous_const.mul continuous_id).continuousAt
    exact this.preimage_mem_nhds (by rw [inv_mul_cancel]; exact isOpen_W.mem_nhds one_W)
  refine (continuousAt_const (y := c0 g)).congr ?_
  filter_upwards [hW] with h hh
  have hξ := Classical.choose_spec (dec g)
  set ξ := Classical.choose (dec g)
  have e : principalIdele ℚ ξ * h = (principalIdele ℚ ξ * g) * (g⁻¹ * h) := by
    rw [mul_assoc, mul_inv_cancel_left]
  have hU : principalIdele ℚ ξ * h ∈ Up := by rw [e]; exact Up_mul hξ hh.1
  show c0 g = c0 h
  rw [c0_eq hU, e, χ_mul hξ.2 hh.1.2, χ_W hh, mul_one, c0_eq hξ]

lemma c0_norm (g : IQ) : ‖c0 g‖ = 1 := χ_norm _

lemma c0_qc : IsQuasiCharacter c0 :=
  ⟨c0_cont, c0_mul, fun g => χ_ne _, c0_principal⟩

/-- the idele `(1, -1, -1, …)` -/
def tI : IQ where
  val := ((1, -1) : InfiniteAdeleRing ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ)
  inv := ((1, -1) : InfiniteAdeleRing ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ)
  val_inv := by
    show ((1 * 1, -1 * -1) : InfiniteAdeleRing ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ) = (1, 1)
    rw [mul_one, neg_mul_neg, mul_one]
  inv_val := by
    show ((1 * 1, -1 * -1) : InfiniteAdeleRing ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ) = (1, 1)
    rw [mul_one, neg_mul_neg, mul_one]

lemma tI_Up : tI ∈ Up := by
  refine ⟨?_, fun v => ?_⟩
  · show 0 < ιr w0 (1 : w0.Completion); rw [map_one]; exact one_pos
  · show Valued.v (-1 : v.adicCompletion ℚ) = 1
    rw [Valuation.map_neg, map_one]

lemma tI_norm : ideleNorm tI = 1 := by
  rw [ideleNorm_Up tI_Up.2]
  show |ιr w0 (1 : w0.Completion)| = 1
  rw [map_one, abs_one]

lemma c0_tI : c0 tI ≠ 1 := by
  have e : principalIdele ℚ 1 * tI = tI := by rw [map_one, one_mul]
  have hU : principalIdele ℚ 1 * tI ∈ Up := by rw [e]; exact tI_Up
  rw [c0_eq hU, e]
  have hm := mem3 tI_Up.2
  have hx : (⟨(tI : AQ).2 v3, hm⟩ : v3.adicCompletionIntegers ℚ) = -1 := rfl
  unfold χ z
  rw [dif_pos hm, hx, map_neg, map_one, map_neg, map_one]
  have : (-1 : ZMod 3) ≠ 1 := by decide
  rw [if_neg this]; norm_num

end

end Aux_GZ


namespace Aux_GZ

open MasulloGRH NumberField IsDedekindDomain Filter Topology Aux_LFA
open Aux_MasulloGRH_idele_class_group_topology
open scoped WithZero

noncomputable section

local notation "AQ" => AdeleRing (𝓞 ℚ) ℚ
local notation "IQ" => IdeleGroup ℚ

instance adTG : IsTopologicalAddGroup AQ :=
  inferInstanceAs (IsTopologicalAddGroup (InfiniteAdeleRing ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ))

/-- `ℝ^d × 𝔸_f ≅ 𝔸` -/
def eQ : ((Fin (dimV ℚ) → ℝ) × FiniteAdeleRing (𝓞 ℚ) ℚ) ≃+ AQ :=
  AddEquiv.prodCongr (eV ℚ).symm (AddEquiv.refl _)

/-- the setup for the adeles of `ℚ` -/
def SQ : Setup AQ (FiniteAdeleRing (𝓞 ℚ) ℚ) (dimV ℚ) :=
  ringSetup (finRD ℚ) eQ ((cont_eV_symm ℚ).prodMap continuous_id)
    ((cont_eV ℚ).prodMap continuous_id)

/-- a bump function -/
def bmp : ContDiffBump (0 : Fin (dimV ℚ) → ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

/-- the archimedean factor -/
def φ0 (x : Fin (dimV ℚ) → ℝ) : ℝ := bmp x

lemma φ0_nonneg (x : Fin (dimV ℚ) → ℝ) : 0 ≤ φ0 x := bmp.nonneg

lemma φ0_zero : φ0 0 = 1 :=
  bmp.one_of_mem_closedBall (Metric.mem_closedBall_self (by norm_num [bmp]))

lemma φ0_cont : Continuous φ0 := bmp.continuous

/-- the function on `ℝ^d × ℝ^0` -/
def hfun (xt : (Fin (dimV ℚ) → ℝ) × (Fin 0 → ℝ)) : ℂ := ((φ0 xt.1 : ℝ) : ℂ)

lemma hfun_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) hfun :=
  Complex.ofRealCLM.contDiff.comp (bmp.contDiff.comp contDiff_fst)

lemma hfun_cs : HasCompactSupport hfun := by
  have hK : IsCompact (tsupport φ0 ×ˢ (Set.univ : Set (Fin 0 → ℝ))) :=
    bmp.hasCompactSupport.isCompact.prod (Set.toFinite _).isCompact
  refine hK.of_isClosed_subset (isClosed_tsupport _) (closure_minimal ?_
    ((isClosed_tsupport _).prod isClosed_univ))
  intro xt hxt
  refine ⟨subset_tsupport _ ?_, Set.mem_univ _⟩
  intro h0
  exact hxt (by simp [hfun, h0])

/-- the elementary Schwartz function -/
def gfun (q : ElemGroup (dimV ℚ) 0 0 (SQ.sN 0) (SQ.dN 0)) : ℂ := ((φ0 q.1 : ℝ) : ℂ)

lemma gfun_rd : IsRapidDecay gfun := by
  refine ⟨fun a b => hfun_smooth, fun i j k => ?_⟩
  let Φ := hfun_cs.toSchwartzMap hfun_smooth
  refine ⟨SchwartzMap.seminorm ℝ i k Φ, fun a b xt => ?_⟩
  have ha : ‖a‖ ^ j ≤ 1 := by
    have : a = 0 := Subsingleton.elim _ _
    rw [this, norm_zero]
    rcases Nat.eq_zero_or_pos j with h | h
    · rw [h, pow_zero]
    · rw [zero_pow h.ne']; exact zero_le_one
  have h1 : ‖xt‖ ^ i * ‖iteratedFDeriv ℝ k hfun xt‖ ≤ SchwartzMap.seminorm ℝ i k Φ :=
    SchwartzMap.le_seminorm ℝ i k Φ xt
  have h2 : ‖xt.1‖ ^ i ≤ ‖xt‖ ^ i := pow_le_pow_left₀ (norm_nonneg _) (norm_fst_le xt) i
  show ‖a‖ ^ j * ‖xt.1‖ ^ i * ‖iteratedFDeriv ℝ k hfun xt‖ ≤ _
  calc ‖a‖ ^ j * ‖xt.1‖ ^ i * ‖iteratedFDeriv ℝ k hfun xt‖
      ≤ 1 * ‖xt‖ ^ i * ‖iteratedFDeriv ℝ k hfun xt‖ := by gcongr
    _ ≤ _ := by rw [one_mul]; exact h1

/-- the element of `S(ℝ^d)` -/
def yQ : ElemSchwartz (dimV ℚ) 0 0 (SQ.sN 0) (SQ.dN 0) := ⟨gfun, Submodule.subset_span gfun_rd⟩

/-- the Schwartz–Bruhat function `φ(x_∞) 1_{\hat ℤ}(x_f)` -/
def fQ : AdelicSchwartz ℚ :=
  SchwartzBruhat.ofElem (SQ.Gam 0) (SQ.Kk 0) (SQ.pres 0) (SQ.stage_sp 0) (SQ.pres_isElem 0) yQ

open Classical in
lemma fQ_eval (x : AQ) : fQ.eval x =
    if x.2 ∈ finO ℚ then ((φ0 (eV ℚ x.1) : ℝ) : ℂ) else 0 := by
  show extendPullback (SQ.Gam 0) (SQ.pres 0) gfun (Multiplicative.ofAdd x) = _
  unfold extendPullback
  have hmem : (Multiplicative.ofAdd x ∈ SQ.Gam 0) ↔ x.2 ∈ finO ℚ := by
    show ((Nat.factorial 0 : ℕ) : FiniteAdeleRing (𝓞 ℚ) ℚ) * x.2 ∈ finO ℚ ↔ x.2 ∈ finO ℚ
    rw [Nat.factorial_zero, Nat.cast_one, one_mul]
  by_cases h : x.2 ∈ finO ℚ
  · rw [dif_pos (hmem.2 h), if_pos h]; rfl
  · rw [dif_neg (fun h' => h (hmem.1 h')), if_neg h]

lemma fQ_zero : fQ.eval 0 = 1 := by
  rw [fQ_eval]
  split_ifs with h
  · show ((φ0 (eV ℚ 0) : ℝ) : ℂ) = 1
    rw [map_zero, φ0_zero, Complex.ofReal_one]
  · exact absurd (zero_mem (finO ℚ)) h

/-- real parametrisation of the infinite adeles -/
def sR (t : ℝ) : InfiniteAdeleRing ℚ := fun w => (ιr w).symm t

lemma sR_cont : Continuous sR := continuous_pi fun w => ιr_symm_cont w

lemma sR_eq (x : InfiniteAdeleRing ℚ) : sR (ιr w0 (x w0)) = x := by
  funext w
  have hw : w = w0 := Subsingleton.elim _ _
  subst hw
  exact (ιr w0).symm_apply_apply _

/-- the archimedean factor as a function of a real variable -/
def φr (t : ℝ) : ℝ := φ0 (eV ℚ (sR t))

lemma φr_cont : Continuous φr := φ0_cont.comp ((cont_eV ℚ).comp sR_cont)

lemma φr_zero : φr 0 = 1 := by
  have : sR 0 = 0 := funext fun w => map_zero (ιr w).symm
  rw [φr, this, map_zero, φ0_zero]

open Classical in
lemma fQ_eval' (g : IQ) : fQ.eval (g : AQ) =
    if (g : AQ).2 ∈ finO ℚ then ((φr (inf g) : ℝ) : ℂ) else 0 := by
  rw [fQ_eval]
  unfold φr inf
  rw [sR_eq]

lemma φr_bound : ∃ R : ℝ, ∀ t, φr t ≠ 0 → |t| ≤ R := by
  have hG : Continuous (fun y : Fin (dimV ℚ) → ℝ => ιr w0 ((eV ℚ).symm y w0)) :=
    (ιr_cont w0).comp ((continuous_apply w0).comp (cont_eV_symm ℚ))
  obtain ⟨C, hC⟩ := bmp.hasCompactSupport.isCompact.exists_bound_of_continuousOn hG.continuousOn
  refine ⟨C, fun t ht => ?_⟩
  have hm : eV ℚ (sR t) ∈ tsupport φ0 := subset_tsupport _ ht
  have := hC _ hm
  rw [AddEquiv.symm_apply_apply] at this
  have e : ιr w0 (sR t w0) = t := (ιr w0).apply_symm_apply t
  rw [e, Real.norm_eq_abs] at this
  exact this

lemma φr_pos : ∃ ε > 0, ∀ t, |t| < ε → 1 / 2 < φr t := by
  have := Metric.continuousAt_iff.1 (φr_cont.continuousAt (x := 0)) (1 / 2) (by norm_num)
  obtain ⟨δ, hδ, h⟩ := this
  refine ⟨δ, hδ, fun t ht => ?_⟩
  have := h (show dist t 0 < δ by rw [Real.dist_eq, sub_zero]; exact ht)
  rw [φr_zero, Real.dist_eq, abs_lt] at this
  linarith

lemma term_eq (η : ℚˣ) (g : IQ) :
    fQ.eval (algebraMap ℚ AQ (η : ℚ) * (g : AQ)) = fQ.eval ((principalIdele ℚ η * g : IQ) : AQ) :=
  rfl

lemma term_nonneg (g : IQ) : 0 ≤ (fQ.eval (g : AQ)).re := by
  rw [fQ_eval']; split_ifs
  · rw [Complex.ofReal_re]; exact φ0_nonneg _
  · simp

lemma theta_summable (g : IQ) :
    (Function.support fun η : ℚˣ => fQ.eval (algebraMap ℚ AQ (η : ℚ) * (g : AQ))).Finite := by
  obtain ⟨R, hR⟩ := φr_bound
  have hξ := Classical.choose_spec (dec g)
  set ξ := Classical.choose (dec g)
  set h := principalIdele ℚ ξ * g
  have ha : 0 < inf h := hξ.1
  set K : ℝ := R / inf h
  let S : Set ℚˣ := {η | ∃ n : ℤ, |(n : ℝ)| ≤ K ∧ (η : ℚ) = n * (ξ : ℚ)}
  have hsub : (Function.support fun η : ℚˣ => fQ.eval (algebraMap ℚ AQ (η : ℚ) * (g : AQ))) ⊆ S := by
    intro η hη
    rw [Function.mem_support, term_eq] at hη
    have e : principalIdele ℚ η * g = principalIdele ℚ (η * ξ⁻¹) * h := by
      simp only [h, map_mul, map_inv]; group
    rw [fQ_eval', e] at hη
    by_cases hf : ((principalIdele ℚ (η * ξ⁻¹) * h : IQ) : AQ).2 ∈ finO ℚ
    · rw [if_pos hf] at hη
      have hφ : φr (inf (principalIdele ℚ (η * ξ⁻¹) * h)) ≠ 0 := fun h0 => hη (by rw [h0]; simp)
      have hv : ∀ v : HeightOneSpectrum (𝓞 ℚ), v.valuation ℚ ((η * ξ⁻¹ : ℚˣ) : ℚ) ≤ 1 := by
        intro v
        have h1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hf v)
        rw [val_comp, hξ.2 v, mul_one] at h1
        exact h1
      obtain ⟨n, hn⟩ := int_of_val _ hv
      refine ⟨n, ?_, ?_⟩
      · have := hR _ hφ
        rw [inf_principal, ← hn, abs_mul, abs_of_pos ha] at this
        push_cast at this
        rw [le_div_iff₀ ha]; exact this
      · rw [hn]; simp
    · rw [if_neg hf] at hη; exact absurd rfl hη
  refine Set.Finite.subset ?_ hsub
  apply Set.Finite.of_finite_image (f := (Units.val : ℚˣ → ℚ)) _ (Units.val_injective.injOn)
  refine ((Set.finite_Icc (-⌈K⌉) ⌈K⌉).image (fun n : ℤ => (n : ℚ) * (ξ : ℚ))).subset ?_
  rintro _ ⟨η, ⟨n, hn, he⟩, rfl⟩
  refine ⟨n, ?_, he.symm⟩
  have h1 : |(n : ℝ)| ≤ (⌈K⌉ : ℝ) := hn.trans (Int.le_ceil K)
  have h2 : |n| ≤ ⌈K⌉ := by exact_mod_cast h1
  exact abs_le.1 h2

lemma theta_low : ∃ ε > 0, ∀ g : IQ, ideleNorm g < ε → 1 / 2 ≤ ‖adelicTheta fQ g‖ := by
  obtain ⟨ε, hε, hφ⟩ := φr_pos
  refine ⟨ε, hε, fun g hg => ?_⟩
  have hξ := Classical.choose_spec (dec g)
  set ξ := Classical.choose (dec g)
  have hfin := theta_summable g
  have hs : Summable fun η : ℚˣ => fQ.eval (algebraMap ℚ AQ (η : ℚ) * (g : AQ)) :=
    summable_of_hasFiniteSupport hfin
  have hs' : Summable fun η : ℚˣ => (fQ.eval (algebraMap ℚ AQ (η : ℚ) * (g : AQ))).re := by
    refine summable_of_hasFiniteSupport (hfin.subset fun η hη => ?_)
    intro h0; apply hη; simp only at h0 ⊢; rw [h0, Complex.zero_re]
  have hre : (adelicTheta fQ g).re = ∑' η : ℚˣ, (fQ.eval (algebraMap ℚ AQ (η : ℚ) * (g : AQ))).re :=
    Complex.re_tsum hs
  have hle := hs'.le_tsum ξ (fun j _ => by rw [term_eq]; exact term_nonneg _)
  have hterm : 1 / 2 < (fQ.eval (algebraMap ℚ AQ (ξ : ℚ) * (g : AQ))).re := by
    rw [term_eq, fQ_eval']
    have hfO : ((principalIdele ℚ ξ * g : IQ) : AQ).2 ∈ finO ℚ := fun v =>
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (hξ.2 v).le
    rw [if_pos hfO, Complex.ofReal_re]
    apply hφ
    rw [← ideleNorm_Up hξ.2, ideleNorm_mul, ideleNorm_principal, one_mul]
    exact hg
  have := Complex.re_le_norm (adelicTheta fQ g)
  linarith

end

end Aux_GZ


namespace Aux_GZ

open MasulloGRH NumberField IsDedekindDomain Filter Topology MeasureTheory
open Aux_MasulloGRH_idele_class_group_topology
open scoped WithZero Pointwise

noncomputable section

local notation "AQ" => AdeleRing (𝓞 ℚ) ℚ
local notation "IQ" => IdeleGroup ℚ
local notation "CQ" => IdeleClassGroup ℚ

lemma norm_exists {a : ℝ} (ha : 0 < a) : ∃ g : IQ, ideleNorm g = a := by
  obtain ⟨f, -, hfn⟩ := exists_scalar w0
  exact ⟨sv w0 f (Real.log a), by rw [ideleNorm_sv w0 f hfn, Real.exp_log ha]⟩

/-- the norm on the idele class group -/
def Nc (x : CQ) : ℝ := ideleNorm x.out

lemma Nc_mk (g : IQ) : Nc (QuotientGroup.mk g) = ideleNorm g := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (principalIdeles ℚ) g
  unfold Nc
  rw [hh, ideleNorm_mul]
  obtain ⟨ξ, hξ⟩ := h.2
  rw [← hξ, ideleNorm_principal, mul_one]

lemma Nc_cont : Continuous Nc := by
  refine (QuotientGroup.isQuotientMap_mk (principalIdeles ℚ)).continuous_iff.2 ?_
  have : Nc ∘ (QuotientGroup.mk : IQ → CQ) = ideleNorm := funext Nc_mk
  rw [this]; exact ideleNorm_continuous

lemma Nc_mul (x y : CQ) : Nc (x * y) = Nc x * Nc y := by
  induction x using QuotientGroup.induction_on with
  | H g =>
  induction y using QuotientGroup.induction_on with
  | H h => rw [← QuotientGroup.mk_mul, Nc_mk, Nc_mk, Nc_mk, ideleNorm_mul]

lemma Nc_pos (x : CQ) : 0 < Nc x := ideleNorm_pos _

lemma strip_eq : (QuotientGroup.mk : IQ → CQ) '' {g | 1 ≤ ideleNorm g ∧ ideleNorm g < Real.exp 1} =
    Nc ⁻¹' Set.Ico 1 (Real.exp 1) := by
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    show Nc (QuotientGroup.mk g) ∈ Set.Ico 1 (Real.exp 1)
    rw [Nc_mk]; exact hg
  · intro hx
    induction x using QuotientGroup.induction_on with
    | H g =>
      refine ⟨g, ?_, rfl⟩
      have : Nc (QuotientGroup.mk g) ∈ Set.Ico 1 (Real.exp 1) := hx
      rw [Nc_mk] at this; exact this

lemma meas_Nc (s : Set ℝ) (hs : MeasurableSet s) : MeasurableSet (Nc ⁻¹' s) :=
  Nc_cont.measurable hs

section genuine

variable (μ : Measure CQ) [μ.IsHaarMeasure]
  (hV : μ (Nc ⁻¹' Set.Ico 1 (Real.exp 1)) = ENNReal.ofReal (tamagawaClassVolume ℚ))
include hV

lemma meas_band {a : ℝ} (ha : 0 < a) :
    μ (Nc ⁻¹' Set.Ico a (a * Real.exp 1)) = ENNReal.ofReal (tamagawaClassVolume ℚ) := by
  obtain ⟨g, hg⟩ := norm_exists ha
  set c : CQ := QuotientGroup.mk g
  have hc : Nc c = a := by rw [Nc_mk, hg]
  have hci : Nc c⁻¹ = a⁻¹ := by
    have := Nc_mul c⁻¹ c
    rw [inv_mul_cancel, hc] at this
    have h1 : Nc 1 = 1 := by
      have := Nc_mk (1 : IQ); rw [QuotientGroup.mk_one] at this; rw [this]
      rw [ideleNorm_eq_infNorm 1 (fun v => (at_iff 1 v).1 (one_Up.2 v)), prod_inf, inf_one, abs_one]
    rw [h1] at this
    field_simp; linarith
  have e : Nc ⁻¹' Set.Ico a (a * Real.exp 1) =
      (fun x => c⁻¹ * x) ⁻¹' (Nc ⁻¹' Set.Ico 1 (Real.exp 1)) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Ico]
    rw [Nc_mul, hci, le_inv_mul_iff₀ ha, inv_mul_lt_iff₀ ha, mul_one]
  rw [e, measure_preimage_mul, hV]

lemma meas_union_band {a : ℝ} (ha : 0 < a) (n : ℕ) :
    μ (Nc ⁻¹' Set.Ico (a * Real.exp (-(n : ℝ))) a) = n * ENNReal.ofReal (tamagawaClassVolume ℚ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : a * Real.exp (-((n + 1 : ℕ) : ℝ)) ≤ a * Real.exp (-(n : ℝ)) := by
      gcongr; push_cast; linarith
    have h2 : a * Real.exp (-(n : ℝ)) ≤ a := by
      have : Real.exp (-(n : ℝ)) ≤ 1 := Real.exp_le_one_iff.2 (by simp)
      nlinarith
    rw [← Set.Ico_union_Ico_eq_Ico h1 h2, Set.preimage_union,
      measure_union ((Set.Ico_disjoint_Ico_same).preimage Nc) (meas_Nc _ measurableSet_Ico), ih]
    have hb : 0 < a * Real.exp (-((n + 1 : ℕ) : ℝ)) := mul_pos ha (Real.exp_pos _)
    have e : a * Real.exp (-(n : ℝ)) = a * Real.exp (-((n + 1 : ℕ) : ℝ)) * Real.exp 1 := by
      rw [mul_assoc, ← Real.exp_add]; push_cast; ring_nf
    rw [e, meas_band μ hV hb]
    push_cast; ring

lemma genuine_false :
    ¬ Integrable (fun x : CQ => adelicTheta fQ x.out * quasiTwist c0 0 x.out) μ := by
  intro hint
  obtain ⟨ε, hε, hlow⟩ := theta_low
  set V := tamagawaClassVolume ℚ
  have hVpos : 0 < V := NumberField.dedekindZeta_residue_pos ℚ
  set L := ∫⁻ x, ‖adelicTheta fQ x.out * quasiTwist c0 0 x.out‖ₑ ∂μ
  have hL : L < ⊤ := hint.2
  have hbound : ∀ n : ℕ, ENNReal.ofReal (1 / 2) * (n * ENNReal.ofReal V) ≤ L := by
    intro n
    have ha : 0 < ε / 2 := by linarith
    rw [← meas_union_band μ hV ha n, ← lintegral_indicator_const (meas_Nc _ measurableSet_Ico)]
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ Nc ⁻¹' Set.Ico (ε / 2 * Real.exp (-(n : ℝ))) (ε / 2)
    · rw [Set.indicator_of_mem hx, ← ofReal_norm_eq_enorm]
      apply ENNReal.ofReal_le_ofReal
      have hn : ideleNorm x.out < ε := by
        have : Nc x < ε / 2 := hx.2
        unfold Nc at this; linarith
      have h1 := hlow _ hn
      have h2 : ‖quasiTwist c0 0 x.out‖ = 1 := by
        unfold quasiTwist normQuasiChar
        rw [Complex.cpow_zero, mul_one, c0_norm]
      rw [norm_mul, h2, mul_one]; exact h1
    · rw [Set.indicator_of_notMem hx]; exact zero_le'
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * L.toReal / V)
  have := hbound n
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_le_iff_le_toReal hL.ne] at this
  rw [div_lt_iff₀ hVpos] at hn
  linarith

end genuine

/-- the trivial quasi-character -/
lemma qc_one : IsQuasiCharacter (fun _ : IQ => (1 : ℂ)) :=
  ⟨continuous_const, fun _ _ => (mul_one 1).symm, fun _ => one_ne_zero, fun _ => rfl⟩

lemma qa_dual_one : quasiAbscissa (quasiDual (fun _ : IQ => (1 : ℂ))) = 1 := by
  have hex : ∃ σ : ℝ, ∀ g : IQ, ‖quasiDual (fun _ : IQ => (1 : ℂ)) g‖ = ideleNorm g ^ σ :=
    ⟨1, fun g => by
      simp only [quasiDual, inv_one, mul_one, Complex.norm_real, Real.norm_eq_abs, Real.rpow_one]
      exact abs_of_pos (ideleNorm_pos g)⟩
  unfold quasiAbscissa
  rw [dif_pos hex]
  have hs := hex.choose_spec
  generalize hex.choose = σ at hs ⊢
  obtain ⟨g, hg⟩ := norm_exists (show (0 : ℝ) < 2 by norm_num)
  have h0 := hs g
  simp only [quasiDual, inv_one, mul_one, Complex.norm_real, Real.norm_eq_abs, hg] at h0
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h0
  have h2 : Real.log 2 = σ * Real.log 2 := by
    conv_lhs => rw [h0]
    exact Real.log_rpow (by norm_num) σ
  have hl : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have := mul_right_cancel₀ hl (h2.symm.trans (one_mul _).symm)
  exact this

lemma tamagawaIdele_zero (hcls : tamagawaIdeleClass ℚ = 0) : tamagawaIdele ℚ = 0 := by
  unfold tamagawaIdele
  rw [dif_neg]
  rintro ⟨μ, hH, hD⟩
  have hinj : Set.InjOn (QuotientGroup.mk : IQ → CQ) Up := by
    intro a ha b hb hab
    have h1 : a⁻¹ * b ∈ principalIdeles ℚ := QuotientGroup.eq.1 hab
    obtain ⟨ξ, hξ⟩ := h1
    have h2 : principalIdele ℚ ξ ∈ Up := by rw [hξ]; exact Up_mul (Up_inv ha) hb
    have h3 := uq ξ h2
    rw [h3, map_one] at hξ
    exact (inv_mul_eq_one.1 hξ.symm)
  have h1 := hD Up isOpen_Up.measurableSet hinj
  rw [hcls, Measure.coe_zero, Pi.zero_apply] at h1
  exact (isOpen_Up.measure_pos μ ⟨1, one_Up⟩).ne' h1

lemma junk_false (htI : tamagawaIdele ℚ = 0) (M M' : ℂ → ℂ)
    (hres : Tendsto (fun s : ℂ => (s - 0) * M s) (𝓝[≠] 0)
      (𝓝 (-(tamagawaClassVolume ℚ : ℂ) * fQ.eval 0)))
    (hM' : ∀ s : ℂ, 1 < quasiAbscissa (quasiDual (fun _ : IQ => (1 : ℂ))) + s.re →
      M' s = zetaIntegralFun (adelicFourier fQ) (quasiTwist (quasiDual (fun _ : IQ => (1 : ℂ))) s))
    (hMM : ∀ s : ℂ, M s = M' (-s)) : False := by
  have hk : Tendsto (fun t : ℝ => -(t : ℂ)) (𝓝[>] 0) (𝓝[≠] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have : Tendsto (fun t : ℝ => -(t : ℂ)) (𝓝 0) (𝓝 (-((0 : ℝ) : ℂ))) :=
        (Complex.continuous_ofReal.neg).tendsto 0
      rw [Complex.ofReal_zero, neg_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff, neg_eq_zero, Complex.ofReal_eq_zero]
      exact (ne_of_gt ht)
  have h1 := hres.comp hk
  have hzero : (fun t : ℝ => ((-(t : ℂ)) - 0) * M (-(t : ℂ))) =ᶠ[𝓝[>] 0] fun _ => 0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : (0 : ℝ) < t := ht
    rw [hMM, neg_neg, hM' _ (by rw [qa_dual_one, Complex.ofReal_re]; linarith)]
    unfold zetaIntegralFun
    rw [htI, integral_zero_measure, mul_zero]
  have h3 : Tendsto (fun t : ℝ => ((-(t : ℂ)) - 0) * M (-(t : ℂ))) (𝓝[>] 0) (𝓝 0) :=
    tendsto_const_nhds.congr' hzero.symm
  have h4 := tendsto_nhds_unique h1 h3
  rw [fQ_zero, mul_one, neg_eq_zero, Complex.ofReal_eq_zero] at h4
  exact (NumberField.dedekindZeta_residue_pos ℚ).ne' h4

end

end Aux_GZ


open MasulloGRH NumberField IsDedekindDomain MeasureTheory Aux_GZ in
theorem solution : ¬ (∀ (F : Type) [Field F] [NumberField F] (f : AdelicSchwartz F)
    (c₀ : IdeleGroup F → ℂ) (hc : IsQuasiCharacter c₀),
    ((∀ s : ℂ, 1 < quasiAbscissa c₀ + s.re →
        Integrable (fun g : IdeleGroup F => f.eval (g : AdeleRing (𝓞 F) F) * quasiTwist c₀ s g)
          (tamagawaIdele F)) ∧
      DifferentiableOn ℂ (fun s : ℂ => zetaIntegral f (quasiTwist c₀ s))
        {s : ℂ | 1 < quasiAbscissa c₀ + s.re}) ∧
    (∃ M M' : ℂ → ℂ, MeromorphicNFOn M Set.univ ∧ MeromorphicNFOn M' Set.univ ∧
      (∀ s : ℂ, 1 < quasiAbscissa c₀ + s.re → M s = zetaIntegral f (quasiTwist c₀ s)) ∧
      (∀ s : ℂ, quasiTwist c₀ s ≠ (fun _ => 1) → quasiTwist c₀ s ≠ normQuasiChar 1 →
        AnalyticAt ℂ M s) ∧
      (∀ s₀ : ℂ, quasiTwist c₀ s₀ = (fun _ => 1) →
        Filter.Tendsto (fun s : ℂ => (s - s₀) * M s) (nhdsWithin s₀ {s₀}ᶜ)
          (nhds (-(tamagawaClassVolume F : ℂ) * f.eval 0))) ∧
      (∀ s₀ : ℂ, quasiTwist c₀ s₀ = normQuasiChar 1 →
        Filter.Tendsto (fun s : ℂ => (s - s₀) * M s) (nhdsWithin s₀ {s₀}ᶜ)
          (nhds ((tamagawaClassVolume F : ℂ) * adelicFourier f 0))) ∧
      (∀ s : ℂ, 1 < quasiAbscissa (quasiDual c₀) + s.re →
        M' s = zetaIntegralFun (adelicFourier f) (quasiTwist (quasiDual c₀) s)) ∧
      ∀ s : ℂ, M s = M' (-s)) ∧
    (∀ s : ℂ, 1 < quasiAbscissa c₀ + s.re →
      Integrable (fun x : IdeleClassGroup F => adelicTheta f x.out * quasiTwist c₀ s x.out)
        (tamagawaIdeleClass F) ∧
      thetaMellin f (quasiTwist c₀ s) = zetaIntegral f (quasiTwist c₀ s)) ∧
    ((f.IsPolarFree ∨ ¬ ∀ g : IdeleGroup F, ideleNorm g = 1 → c₀ g = 1) →
      (∀ s : ℂ,
        Integrable (fun x : IdeleClassGroup F => adelicTheta f x.out * quasiTwist c₀ s x.out)
          (tamagawaIdeleClass F)) ∧
      Differentiable ℂ (fun s : ℂ => thetaMellin f (quasiTwist c₀ s)))) := by
  intro H
  by_cases hμ : ∃ μ : Measure (IdeleClassGroup ℚ), μ.IsHaarMeasure ∧
      μ ((QuotientGroup.mk : IdeleGroup ℚ → IdeleClassGroup ℚ) ''
        {g | 1 ≤ ideleNorm g ∧ ideleNorm g < Real.exp 1}) =
        ENNReal.ofReal (tamagawaClassVolume ℚ)
  · -- genuine Tamagawa measure: the absolute-convergence claim of (2b) fails
    have hT : tamagawaIdeleClass ℚ = hμ.choose := by
      unfold tamagawaIdeleClass; rw [dif_pos hμ]
    have hH : (tamagawaIdeleClass ℚ).IsHaarMeasure := hT ▸ hμ.choose_spec.1
    have hV : tamagawaIdeleClass ℚ (Nc ⁻¹' Set.Ico 1 (Real.exp 1)) =
        ENNReal.ofReal (tamagawaClassVolume ℚ) := by
      rw [← strip_eq, hT]; exact hμ.choose_spec.2
    have hnt : ¬ ∀ g : IdeleGroup ℚ, ideleNorm g = 1 → c0 g = 1 := fun h => c0_tI (h tI tI_norm)
    have h2b := ((H ℚ fQ c0 c0_qc).2.2.2 (Or.inr hnt)).1 0
    exact genuine_false (tamagawaIdeleClass ℚ) hV h2b
  · -- no such measure: the Tamagawa measures are `0` and the residue at `s = 0` is `0`
    have hcls : tamagawaIdeleClass ℚ = 0 := by
      unfold tamagawaIdeleClass; rw [dif_neg hμ]
    have htI := tamagawaIdele_zero hcls
    obtain ⟨-, ⟨M, M', -, -, -, -, hres, -, hM', hMM⟩, -⟩ := H ℚ fQ (fun _ => 1) qc_one
    have h1 : quasiTwist (fun _ : IdeleGroup ℚ => (1 : ℂ)) 0 = fun _ => 1 := by
      funext g; simp [quasiTwist, normQuasiChar]
    exact junk_false htI M M' (hres 0 h1) hM' hMM

