-- Prove2me | solution 1 for MasulloGRH.idele_group_topology
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T05:33:12.961902+00:00
-- url     : https://prove2.me/submissions/9ab25000-8b18-427e-a4c9-2d2e24a7484d

import Definitions.Def_MasulloGRH_IdeleNorm

set_option autoImplicit false

open MasulloGRH NumberField IsDedekindDomain

namespace Aux_MasulloGRH_idele_group_topology

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

end Aux_MasulloGRH_idele_group_topology

open Aux_MasulloGRH_idele_group_topology in
theorem solution (F : Type*) [Field F] [NumberField F] :
    T2Space (IdeleGroup F) ∧ LocallyCompactSpace (IdeleGroup F) ∧
    (Continuous
        (RestrictedProduct.unitsEquiv (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) :
          (FiniteAdeleRing (𝓞 F) F)ˣ ≃* _) ∧
      Continuous
        (RestrictedProduct.unitsEquiv (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) :
          (FiniteAdeleRing (𝓞 F) F)ˣ ≃* _).symm) ∧
    Continuous (ideleNorm : IdeleGroup F → ℝ) ∧
    (∀ g h : IdeleGroup F, ideleNorm (g * h) = ideleNorm g * ideleNorm h) ∧
    (∀ g : IdeleGroup F, 0 < ideleNorm g) ∧
    IsClosed {g : IdeleGroup F | ideleNorm g = 1} := by
  refine ⟨inferInstance, inferInstance, ⟨?_, ?_⟩, ideleNorm_continuous, ideleNorm_mul,
    ideleNorm_pos, ?_⟩
  · exact unitsEquiv_continuous (fun v : HeightOneSpectrum (𝓞 F) ↦ v.adicCompletionIntegers F)
      (fun v ↦ isOpen_adicCompletionIntegers v)
  · exact unitsEquiv_symm_continuous (fun v : HeightOneSpectrum (𝓞 F) ↦ v.adicCompletionIntegers F)
  · exact isClosed_singleton.preimage ideleNorm_continuous
