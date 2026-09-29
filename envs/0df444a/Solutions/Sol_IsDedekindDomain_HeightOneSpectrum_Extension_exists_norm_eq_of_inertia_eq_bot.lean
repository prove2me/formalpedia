-- Prove2me | solution 1 for IsDedekindDomain.HeightOneSpectrum.Extension.exists_norm_eq_of_inertia_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/d8d8d4d1-65b5-5542-9187-c24b105dcac4

import Mathlib
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_M4aLocalCFT_VocabDefs
import Theorems.Thm_M4aLocalCFT_unitsDecomp_cohTrivial_of_inertia_eq_bot
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_isAdicComplete_adicCompletionIntegers
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_finite_residueField_adicCompletionIntegers
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDedekindDomain_HeightOneSpectrum_Extension_exists_norm_eq_of_inertia_eq_bot

set_option autoImplicit false

section PartL2

set_option autoImplicit false

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField M4aLocalCFT
open scoped Pointwise

namespace P2mS26L2

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))

abbrev Dec : Subgroup (L ≃ₐ[K] L) := MulAction.stabilizer (L ≃ₐ[K] L) w.1.asIdeal

section Stab

variable {K L v w}

omit [NumberField K] [NumberField L] in
theorem algebraMap_smul (τ : L ≃ₐ[K] L) (x : 𝓞 L) :
    algebraMap (𝓞 L) L (τ • x) = τ (algebraMap (𝓞 L) L x) := rfl

theorem smul_mem_pow_iff {τ : L ≃ₐ[K] L} (hτ : τ ∈ Dec K L v w) (x : 𝓞 L) (n : ℕ) :
    τ • x ∈ w.1.asIdeal ^ n ↔ x ∈ w.1.asIdeal ^ n := by
  have h : τ • w.1.asIdeal ^ n = w.1.asIdeal ^ n := by
    rw [smul_pow', MulAction.mem_stabilizer_iff.mp hτ]
  conv_lhs => rw [← h]
  exact Ideal.smul_mem_pointwise_smul_iff

theorem intValuation_smul {τ : L ≃ₐ[K] L} (hτ : τ ∈ Dec K L v w) (x : 𝓞 L) :
    w.1.intValuation (τ • x) = w.1.intValuation x := by
  by_cases hx : x = 0
  · subst hx
    rw [smul_zero]
  have hτx : τ • x ≠ 0 := (smul_ne_zero_iff_ne τ).mpr hx
  have key : ∀ n : ℕ, w.1.intValuation (τ • x) ≤ WithZero.exp (-(n : ℤ)) ↔
      w.1.intValuation x ≤ WithZero.exp (-(n : ℤ)) := fun n => by
    rw [intValuation_le_pow_iff_mem, intValuation_le_pow_iff_mem, smul_mem_pow_iff hτ]
  rw [intValuation_if_neg _ hτx, intValuation_if_neg _ hx] at key ⊢
  exact le_antisymm ((key _).mpr le_rfl) ((key _).mp le_rfl)

theorem valuation_smul {τ : L ≃ₐ[K] L} (hτ : τ ∈ Dec K L v w) (l : L) :
    w.1.valuation L (τ l) = w.1.valuation L l := by
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 L) l
  rw [map_div₀ τ, ← algebraMap_smul τ a, ← algebraMap_smul τ b, map_div₀, map_div₀,
    valuation_of_algebraMap, valuation_of_algebraMap, valuation_of_algebraMap, valuation_of_algebraMap,
    intValuation_smul hτ, intValuation_smul hτ]

end Stab

section Ext

variable {K L v w}

noncomputable def galW (τ : L ≃ₐ[K] L) : WithVal (w.1.valuation L) ≃+* WithVal (w.1.valuation L) :=
  (WithVal.equiv (w.1.valuation L)).trans (τ.toRingEquiv.trans (WithVal.equiv (w.1.valuation L)).symm)

theorem galW_apply (τ : L ≃ₐ[K] L) (x : WithVal (w.1.valuation L)) :
    galW (w := w) τ x = WithVal.toVal (w.1.valuation L) (τ x.ofVal) := rfl

theorem galW_symm_apply (τ : L ≃ₐ[K] L) (x : WithVal (w.1.valuation L)) :
    (galW (w := w) τ).symm x = WithVal.toVal (w.1.valuation L) (τ.symm x.ofVal) := rfl

theorem v_galW {τ : L ≃ₐ[K] L} (hτ : τ ∈ Dec K L v w) (x : WithVal (w.1.valuation L)) :
    Valued.v (galW (w := w) τ x) = Valued.v x := by
  rw [galW_apply, WithVal.valued_toVal, ← WithVal.apply_ofVal]
  exact valuation_smul hτ _

theorem v_galW_symm {τ : L ≃ₐ[K] L} (hτ : τ ∈ Dec K L v w) (x : WithVal (w.1.valuation L)) :
    Valued.v ((galW (w := w) τ).symm x) = Valued.v x := by
  conv_rhs => rw [← (galW (w := w) τ).apply_symm_apply x]
  rw [v_galW hτ]

theorem uniformContinuous_galW {τ : L ≃ₐ[K] L} (hτ : τ ∈ Dec K L v w) :
    UniformContinuous (galW (w := w) τ) := by
  refine uniformContinuous_of_continuousAt_zero (galW (w := w) τ) ?_
  simp_rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero _ _).tendsto_iff (Valued.hasBasis_nhds_zero _ _),
    true_and, forall_const]
  intro γ
  refine ⟨γ, fun x hx => ?_⟩
  simp only [Set.mem_setOf_eq] at hx ⊢
  rw [Valuation.restrict_lt_iff_lt_embedding] at hx ⊢
  rwa [v_galW hτ]

theorem uniformContinuous_galW_symm {τ : L ≃ₐ[K] L} (hτ : τ ∈ Dec K L v w) :
    UniformContinuous (galW (w := w) τ).symm := by
  refine uniformContinuous_of_continuousAt_zero (galW (w := w) τ).symm ?_
  simp_rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero _ _).tendsto_iff (Valued.hasBasis_nhds_zero _ _),
    true_and, forall_const]
  intro γ
  refine ⟨γ, fun x hx => ?_⟩
  simp only [Set.mem_setOf_eq] at hx ⊢
  rw [Valuation.restrict_lt_iff_lt_embedding] at hx ⊢
  rwa [v_galW_symm hτ]

@[elab_as_elim]
theorem adicCompletion_induction_on {R : Type*} [CommRing R] [IsDedekindDomain R] {F : Type*} [Field F]
    [Algebra R F] [IsFractionRing R F] {u : HeightOneSpectrum R} {p : u.adicCompletion F → Prop}
    (x : u.adicCompletion F) (hp : IsClosed {x | p x})
    (ih : ∀ k : WithVal (u.valuation F), p (k : u.adicCompletion F)) : p x := by
  obtain ⟨y, rfl⟩ := adicCompletion.ofCompletion_surjective F u x
  exact UniformSpace.Completion.induction_on (p := fun y => p (adicCompletion.ofCompletion y)) y
    (hp.preimage (adicCompletion.continuous_ofCompletion F u)) ih

noncomputable def extAut {τ : L ≃ₐ[K] L} (hτ : τ ∈ Dec K L v w) :
    w.1.adicCompletion L ≃+* w.1.adicCompletion L :=
  (adicCompletion.equiv L w.1).trans
    ((UniformSpace.Completion.mapRingEquiv (galW (w := w) τ) (uniformContinuous_galW hτ).continuous
      (uniformContinuous_galW_symm hτ).continuous).trans (adicCompletion.equiv L w.1).symm)

theorem extAut_apply {τ : L ≃ₐ[K] L} (hτ : τ ∈ Dec K L v w) (x : w.1.adicCompletion L) :
    extAut hτ x =
      adicCompletion.ofCompletion (UniformSpace.Completion.map (galW (w := w) τ) x.toCompletion) := rfl

theorem continuous_extAut {τ : L ≃ₐ[K] L} (hτ : τ ∈ Dec K L v w) : Continuous (extAut hτ) := by
  show Continuous fun x => extAut hτ x
  simp_rw [extAut_apply]
  exact (adicCompletion.continuous_ofCompletion L w.1).comp
    (UniformSpace.Completion.continuous_map.comp (adicCompletion.continuous_toCompletion L w.1))

theorem extAut_coe {τ : L ≃ₐ[K] L} (hτ : τ ∈ Dec K L v w) (x : WithVal (w.1.valuation L)) :
    extAut hτ (x : w.1.adicCompletion L) = ((galW (w := w) τ x : WithVal (w.1.valuation L)) : w.1.adicCompletion L) := by
  rw [extAut_apply, adicCompletion.toCompletion_ofCompletion,
    UniformSpace.Completion.map_coe (uniformContinuous_galW hτ)]

theorem extAut_coe_field {τ : L ≃ₐ[K] L} (hτ : τ ∈ Dec K L v w) (l : L) :
    extAut hτ (l : w.1.adicCompletion L) = ((τ l : L) : w.1.adicCompletion L) :=
  extAut_coe hτ _

open WithZeroTopology in
theorem v_extAut {τ : L ≃ₐ[K] L} (hτ : τ ∈ Dec K L v w) (x : w.1.adicCompletion L) :
    Valued.v (extAut hτ x) = Valued.v x := by
  refine adicCompletion_induction_on x ?_ ?_
  · exact isClosed_eq
      ((Valued.continuous_valuation_of_surjective (w.1.valuedAdicCompletion_surjective L)).comp
        (continuous_extAut hτ))
      (Valued.continuous_valuation_of_surjective (w.1.valuedAdicCompletion_surjective L))
  · intro k
    rw [extAut_coe hτ, adicCompletion.valued_ofCompletion, adicCompletion.valued_ofCompletion,
      Valued.valuedCompletion_apply, Valued.valuedCompletion_apply, v_galW hτ]

theorem extAut_algebraMap {τ : L ≃ₐ[K] L} (hτ : τ ∈ Dec K L v w) (c : v.adicCompletion K) :
    extAut hτ (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) c) =
      algebraMap (v.adicCompletion K) (w.1.adicCompletion L) c := by
  refine adicCompletion_induction_on c ?_ ?_
  · exact isClosed_eq ((continuous_extAut hτ).comp (w.adicCompletionSemialgHom_continuous K L))
      (w.adicCompletionSemialgHom_continuous K L)
  · intro k
    show extAut hτ (w.adicCompletionSemialgHom K L k) = w.adicCompletionSemialgHom K L k
    rw [w.adicCompletionSemialgHom_coe K L, extAut_coe_field hτ, AlgEquiv.commutes]

theorem extAut_one_apply (x : w.1.adicCompletion L) :
    extAut (one_mem (Dec K L v w)) x = x := by
  refine adicCompletion_induction_on x ?_ ?_
  · exact isClosed_eq (continuous_extAut _) continuous_id
  · intro k
    rw [extAut_coe]
    rfl

theorem extAut_mul_apply {σ τ : L ≃ₐ[K] L} (hσ : σ ∈ Dec K L v w) (hτ : τ ∈ Dec K L v w)
    (x : w.1.adicCompletion L) :
    extAut (mul_mem hσ hτ) x = extAut hσ (extAut hτ x) := by
  refine adicCompletion_induction_on x ?_ ?_
  · exact isClosed_eq (continuous_extAut _) ((continuous_extAut hσ).comp (continuous_extAut hτ))
  · intro k
    rw [extAut_coe, extAut_coe hτ, extAut_coe hσ]
    rfl

theorem coe_sub_adicCompletion (a b : L) :
    ((a - b : L) : w.1.adicCompletion L) = (a : w.1.adicCompletion L) - (b : w.1.adicCompletion L) :=
  map_sub (algebraMap L (w.1.adicCompletion L)) a b

theorem v_lt_one_of_mem_maximalIdeal {a : w.1.adicCompletionIntegers L}
    (ha : a ∈ IsLocalRing.maximalIdeal (w.1.adicCompletionIntegers L)) :
    Valued.v (a : w.1.adicCompletion L) < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ha
  refine lt_of_le_of_ne ((mem_adicCompletionIntegers (𝓞 L) L w.1).mp a.2) fun h => ha ?_
  have ha0 : (a : w.1.adicCompletion L) ≠ 0 := fun h0 => by
    rw [h0, Valuation.map_zero] at h
    exact zero_ne_one h
  have hinv : (a : w.1.adicCompletion L)⁻¹ ∈ w.1.adicCompletionIntegers L := by
    rw [mem_adicCompletionIntegers, map_inv₀, h, inv_one]
  exact ⟨⟨a, ⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ ha0), Subtype.ext (inv_mul_cancel₀ ha0)⟩, rfl⟩

variable (K L v w)

noncomputable def extHom :
    Dec K L v w →* ((w.1.adicCompletion L) ≃ₐ[v.adicCompletion K] (w.1.adicCompletion L)) where
  toFun τ := { extAut τ.2 with commutes' := extAut_algebraMap τ.2 }
  map_one' := by
    ext x : 1
    exact extAut_one_apply x
  map_mul' σ τ := by
    ext x : 1
    exact extAut_mul_apply σ.2 τ.2 x

variable {K L v w}

theorem extHom_apply (τ : Dec K L v w) (x : w.1.adicCompletion L) : extHom K L v w τ x = extAut τ.2 x := rfl

theorem extHom_injective : Function.Injective (extHom K L v w) := by
  intro σ τ h
  apply Subtype.ext
  apply AlgEquiv.ext
  intro l
  have h1 := AlgEquiv.congr_fun h (l : w.1.adicCompletion L)
  rw [extHom_apply, extHom_apply, extAut_coe_field σ.2, extAut_coe_field τ.2] at h1
  have h2 := UniformSpace.Completion.coe_injective (WithVal (w.1.valuation L))
    (adicCompletion.ofCompletion.inj h1)
  exact WithVal.toVal_injective _ h2

theorem v_extHom (τ : Dec K L v w) (x : w.1.adicCompletion L) : Valued.v (extHom K L v w τ x) = Valued.v x :=
  v_extAut τ.2 x

theorem extHom_mem_decompositionSubgroup (τ : Dec K L v w) :
    extHom K L v w τ ∈ (w.1.adicCompletionIntegers L).decompositionSubgroup (v.adicCompletion K) := by
  rw [MulAction.mem_stabilizer_iff]
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, mem_adicCompletionIntegers,
    mem_adicCompletionIntegers, AlgEquiv.smul_def, v_extHom]

end Ext

section Count

variable {K L v w}
variable [IsGalois K L]

scoped instance liesOver_ext : w.1.asIdeal.LiesOver v.asIdeal := by
  constructor
  have h := congrArg HeightOneSpectrum.asIdeal w.2
  rw [HeightOneSpectrum.under_asIdeal] at h
  exact h.symm

attribute [local instance] Ideal.Quotient.field in
theorem card_Dec :
    Nat.card (Dec K L v w) = v.asIdeal.ramificationIdx' w.1.asIdeal * v.asIdeal.inertiaDeg' w.1.asIdeal := by
  haveI := IsGaloisGroup.of_isFractionRing (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) K L
  haveI : w.1.asIdeal.IsMaximal := w.1.isMaximal
  haveI : Finite ((𝓞 K) ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  rw [Ideal.card_stabilizer_eq (G := L ≃ₐ[K] L) v.asIdeal w.1.asIdeal,
    Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal w.1.asIdeal (L ≃ₐ[K] L),
    Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal w.1.asIdeal (L ≃ₐ[K] L),
    ← Ideal.ramificationIdx'_eq_ramificationIdx (p := v.asIdeal) (q := w.1.asIdeal) v.ne_bot,
    ← Ideal.inertiaDeg'_eq_inertiaDeg (p := v.asIdeal) (q := w.1.asIdeal)]

theorem finrank_eq_card_Dec :
    Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) = Nat.card (Dec K L v w) := by
  rw [card_Dec, adicCompletion.ramificationIdx_mul_inertiaDeg_eq_finrank K L w]

theorem card_aut_eq_finrank :
    Nat.card ((w.1.adicCompletion L) ≃ₐ[v.adicCompletion K] (w.1.adicCompletion L)) =
      Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) := by
  apply le_antisymm
  · rw [Nat.card_eq_fintype_card]
    exact AlgEquiv.card_le
  · rw [finrank_eq_card_Dec]
    exact Nat.card_le_card_of_injective _ extHom_injective

theorem isGalois_completion : IsGalois (v.adicCompletion K) (w.1.adicCompletion L) :=
  IsGalois.of_card_aut_eq_finrank _ _ card_aut_eq_finrank

theorem extHom_bijective : Function.Bijective (extHom K L v w) := by
  haveI : Fintype (Dec K L v w) := Fintype.ofFinite _
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨extHom_injective, ?_⟩
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, card_aut_eq_finrank, finrank_eq_card_Dec]

theorem decompositionSubgroup_eq_top :
    (w.1.adicCompletionIntegers L).decompositionSubgroup (v.adicCompletion K) = ⊤ := by
  rw [eq_top_iff]
  intro s _
  obtain ⟨τ, rfl⟩ := extHom_bijective.2 s
  exact extHom_mem_decompositionSubgroup τ

theorem coe_unitsNorm (Y : (w.1.adicCompletionIntegers L)ˣ) :
    (((unitsNorm (K := v.adicCompletion K) (w.1.adicCompletionIntegers L) Y :
        (w.1.adicCompletionIntegers L)ˣ) : w.1.adicCompletionIntegers L) : w.1.adicCompletion L) =
      algebraMap (v.adicCompletion K) (w.1.adicCompletion L)
        (Algebra.norm (v.adicCompletion K) (((Y : w.1.adicCompletionIntegers L)) : w.1.adicCompletion L)) := by
  haveI := isGalois_completion (K := K) (L := L) (v := v) (w := w)
  letI : Fintype ((w.1.adicCompletionIntegers L).decompositionSubgroup (v.adicCompletion K)) := Fintype.ofFinite _
  rw [Algebra.norm_eq_prod_automorphisms,
    ← Fintype.prod_equiv
      ((MulEquiv.subgroupCongr (decompositionSubgroup_eq_top (K := K) (L := L) (v := v) (w := w))).toEquiv.trans
        Subgroup.topEquiv.toEquiv)
      (fun s => (s : (w.1.adicCompletion L) ≃ₐ[v.adicCompletion K] (w.1.adicCompletion L))
        (((Y : w.1.adicCompletionIntegers L)) : w.1.adicCompletion L))
      (fun σ => σ (((Y : w.1.adicCompletionIntegers L)) : w.1.adicCompletion L)) (fun _ => rfl)]
  show (((((∏ s : (w.1.adicCompletionIntegers L).decompositionSubgroup (v.adicCompletion K),
      unitsAct (w.1.adicCompletionIntegers L) s) Y : (w.1.adicCompletionIntegers L)ˣ) :
        w.1.adicCompletionIntegers L) : w.1.adicCompletion L)) = _
  rw [MonoidHom.finsetProd_apply, Units.coe_prod, SubmonoidClass.coe_finsetProd]
  rfl

omit [IsGalois K L] in
theorem v_coe_unit (Y : (w.1.adicCompletionIntegers L)ˣ) :
    Valued.v (((Y : w.1.adicCompletionIntegers L)) : w.1.adicCompletion L) = 1 := by
  apply le_antisymm ((mem_adicCompletionIntegers (𝓞 L) L w.1).mp (Y : w.1.adicCompletionIntegers L).2)
  have h2 : Valued.v (((Y⁻¹ : (w.1.adicCompletionIntegers L)ˣ) : w.1.adicCompletionIntegers L) :
      w.1.adicCompletion L) ≤ 1 :=
    (mem_adicCompletionIntegers (𝓞 L) L w.1).mp ((Y⁻¹ : (w.1.adicCompletionIntegers L)ˣ) : w.1.adicCompletionIntegers L).2
  have h3 : (((Y : w.1.adicCompletionIntegers L)) : w.1.adicCompletion L) *
      (((Y⁻¹ : (w.1.adicCompletionIntegers L)ˣ) : w.1.adicCompletionIntegers L) : w.1.adicCompletion L) = 1 := by
    rw [← Subring.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Subring.coe_one]
  have h4 := congrArg Valued.v h3
  rw [Valuation.map_mul, Valuation.map_one] at h4
  calc (1 : WithZero (Multiplicative ℤ)) = Valued.v (((Y : w.1.adicCompletionIntegers L)) : w.1.adicCompletion L) *
      Valued.v (((Y⁻¹ : (w.1.adicCompletionIntegers L)ˣ) : w.1.adicCompletionIntegers L) : w.1.adicCompletion L) :=
        h4.symm
    _ ≤ Valued.v (((Y : w.1.adicCompletionIntegers L)) : w.1.adicCompletion L) * 1 := by
        gcongr
    _ = _ := mul_one _

end Count

section Unram

variable {K L v w}
variable [IsGalois K L]

attribute [local instance] Ideal.Quotient.field in

theorem isCyclic_Dec (hI : w.1.asIdeal.inertia (L ≃ₐ[K] L) = ⊥) : IsCyclic (Dec K L v w) := by
  haveI : w.1.asIdeal.IsMaximal := w.1.isMaximal
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  haveI : Finite ((𝓞 L) ⧸ w.1.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.1.ne_bot
  apply isCyclic_of_injective (Ideal.Quotient.stabilizerHom w.1.asIdeal v.asIdeal (L ≃ₐ[K] L))
  rw [← MonoidHom.ker_eq_bot_iff, Ideal.Quotient.ker_stabilizerHom]
  show (w.1.asIdeal.inertia (L ≃ₐ[K] L)).subgroupOf _ = ⊥
  rw [hI, Subgroup.bot_subgroupOf]

theorem inertiaSubgroup_loc_eq_bot (hI : w.1.asIdeal.inertia (L ≃ₐ[K] L) = ⊥) :
    (w.1.adicCompletionIntegers L).inertiaSubgroup (v.adicCompletion K) = ⊥ := by
  rw [eq_bot_iff]
  intro s hs
  rw [Subgroup.mem_bot]
  obtain ⟨τ, hτs⟩ : ∃ τ : Dec K L v w, extHom K L v w τ = s.1 := extHom_bijective.2 s.1
  have hs1 : ∀ r : IsLocalRing.ResidueField (w.1.adicCompletionIntegers L), s • r = r := fun r => by
    simpa using RingEquiv.congr_fun (MonoidHom.mem_ker.mp hs) r

  have hτI : (τ : L ≃ₐ[K] L) ∈ w.1.asIdeal.inertia (L ≃ₐ[K] L) := by
    intro x
    have hxA : ((algebraMap (𝓞 L) L x : L) : w.1.adicCompletion L) ∈ w.1.adicCompletionIntegers L :=
      coe_algebraMap_mem (𝓞 L) L w.1 x
    have h1 := hs1 (IsLocalRing.residue _ ⟨_, hxA⟩)
    rw [← IsLocalRing.ResidueField.residue_smul] at h1
    have h2 := Ideal.Quotient.eq.mp h1
    have h3 : ((s • (⟨_, hxA⟩ : w.1.adicCompletionIntegers L) : w.1.adicCompletionIntegers L) :
        w.1.adicCompletion L) = ((algebraMap (𝓞 L) L (τ • x) : L) : w.1.adicCompletion L) := by
      show (s : (w.1.adicCompletion L) ≃ₐ[v.adicCompletion K] (w.1.adicCompletion L))
        ((algebraMap (𝓞 L) L x : L) : w.1.adicCompletion L) = _
      rw [← hτs, extHom_apply, extAut_coe_field, ← algebraMap_smul]
      rfl
    have h4 := v_lt_one_of_mem_maximalIdeal h2
    rw [AddSubgroupClass.coe_sub, h3] at h4
    change Valued.v (((algebraMap (𝓞 L) L (τ • x) : L) : w.1.adicCompletion L) -
      ((algebraMap (𝓞 L) L x : L) : w.1.adicCompletion L)) < 1 at h4
    rw [← coe_sub_adicCompletion, ← map_sub, valuedAdicCompletion_eq_valuation', valuation_lt_one_iff_mem] at h4
    exact h4
  have hτ1 : (τ : L ≃ₐ[K] L) = 1 := by
    rw [hI] at hτI
    exact Subgroup.mem_bot.mp hτI
  apply Subtype.ext
  rw [← hτs, show τ = 1 from Subtype.ext hτ1, map_one, Subgroup.coe_one]

theorem exists_generator_loc (hI : w.1.asIdeal.inertia (L ≃ₐ[K] L) = ⊥) :
    ∃ g : (w.1.adicCompletionIntegers L).decompositionSubgroup (v.adicCompletion K),
      ∀ x, x ∈ Subgroup.zpowers g := by
  haveI := isCyclic_Dec hI
  let f : Dec K L v w →* (w.1.adicCompletionIntegers L).decompositionSubgroup (v.adicCompletion K) :=
    (extHom K L v w).codRestrict _ extHom_mem_decompositionSubgroup
  have hf : Function.Surjective f := by
    rintro ⟨s, hs⟩
    obtain ⟨τ, rfl⟩ := extHom_bijective.2 s
    exact ⟨τ, rfl⟩
  haveI := isCyclic_of_surjective f hf
  exact IsCyclic.exists_generator

end Unram

section Conclusion

variable {K L v w}
variable [IsGalois K L]

theorem exists_unit_norm_eq_of_inertia_eq_bot (hI : w.1.asIdeal.inertia (L ≃ₐ[K] L) = ⊥)
    (u : v.adicCompletion K) (hu : Valued.v u = 1) :
    ∃ y : w.1.adicCompletion L, Valued.v y = 1 ∧ Algebra.norm (v.adicCompletion K) y = u := by
  haveI := IsDedekindDomain.HeightOneSpectrum.isAdicComplete_adicCompletionIntegers L w.1
  haveI : Finite ((𝓞 L) ⧸ w.1.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.1.ne_bot
  haveI := IsDedekindDomain.HeightOneSpectrum.finite_residueField_adicCompletionIntegers L w.1
  obtain ⟨g, hg⟩ := exists_generator_loc (K := K) (L := L) (v := v) (w := w) hI
  haveI : IsCyclic ((w.1.adicCompletionIntegers L).decompositionSubgroup (v.adicCompletion K)) :=
    ⟨⟨g, hg⟩⟩
  have hur := inertiaSubgroup_loc_eq_bot (K := K) (L := L) (v := v) (w := w) hI

  have hxv : Valued.v (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) u) = 1 := by
    rw [show algebraMap (v.adicCompletion K) (w.1.adicCompletion L) u = w.adicCompletionSemialgHom K L u from rfl,
      w.valued_adicCompletionSemialgHom K L u, hu, one_pow]
  have hx0 : algebraMap (v.adicCompletion K) (w.1.adicCompletion L) u ≠ 0 := fun h => by
    rw [h, Valuation.map_zero] at hxv
    exact zero_ne_one hxv
  have hxA : algebraMap (v.adicCompletion K) (w.1.adicCompletion L) u ∈ w.1.adicCompletionIntegers L := by
    rw [mem_adicCompletionIntegers, hxv]
  have hxA' : (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) u)⁻¹ ∈ w.1.adicCompletionIntegers L := by
    rw [mem_adicCompletionIntegers, map_inv₀, hxv, inv_one]
  let X : (w.1.adicCompletionIntegers L)ˣ :=
    ⟨⟨_, hxA⟩, ⟨_, hxA'⟩, Subtype.ext (mul_inv_cancel₀ hx0), Subtype.ext (inv_mul_cancel₀ hx0)⟩

  have hfix : unitsAct (w.1.adicCompletionIntegers L) g X = X := by
    apply Units.ext
    apply Subtype.ext
    exact (g : (w.1.adicCompletion L) ≃ₐ[v.adicCompletion K] (w.1.adicCompletion L)).commutes u
  have hker : X ∈ (unitsDerive (w.1.adicCompletionIntegers L) g).ker := by
    rw [MonoidHom.mem_ker, unitsDerive, MonoidHom.div_apply, MonoidHom.id_apply, hfix, div_self']
  have hXr : X ∈ (unitsNorm (K := v.adicCompletion K) (w.1.adicCompletionIntegers L)).range :=
    (M4aLocalCFT.unitsDecomp_cohTrivial_of_inertia_eq_bot (v.adicCompletion K) (w.1.adicCompletionIntegers L)
      g hg hur).1 hker
  obtain ⟨Y, hY⟩ := hXr
  refine ⟨((Y : w.1.adicCompletionIntegers L) : w.1.adicCompletion L), v_coe_unit Y, ?_⟩
  apply (algebraMap (v.adicCompletion K) (w.1.adicCompletion L)).injective
  rw [← coe_unitsNorm Y, hY]

end Conclusion

end P2mS26L2
p2m_reactivate "P2MW.S_IsDedekindDomain_HeightOneSpectrum_Extension_exists_norm_eq_of_inertia_eq_bot.P2mS26L2"

end PartL2
p2m_reactivate "P2MW.S_IsDedekindDomain_HeightOneSpectrum_Extension_exists_norm_eq_of_inertia_eq_bot.P2mS26L2"

theorem solution
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : v.Extension (NumberField.RingOfIntegers L))
    (hI : w.1.asIdeal.inertia (L ≃ₐ[K] L) = ⊥)
    (u : v.adicCompletion K) (hu : Valued.v u = 1) :
    ∃ y : w.1.adicCompletion L, Valued.v y = 1 ∧ Algebra.norm (v.adicCompletion K) y = u :=
  P2mS26L2.exists_unit_norm_eq_of_inertia_eq_bot (K := K) (L := L) (v := v) (w := w) hI u hu

end S_IsDedekindDomain_HeightOneSpectrum_Extension_exists_norm_eq_of_inertia_eq_bot
end P2MW
export P2MW.S_IsDedekindDomain_HeightOneSpectrum_Extension_exists_norm_eq_of_inertia_eq_bot (solution)
