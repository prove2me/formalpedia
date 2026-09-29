-- Prove2me | solution 1 for IsDedekindDomain.HeightOneSpectrum.Extension.finrank_adicCompletion_eq_one_of_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/7144b72d-937e-5c17-a056-6484caae08d0

import Mathlib
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDedekindDomain_HeightOneSpectrum_Extension_finrank_adicCompletion_eq_one_of_pow_eq

set_option autoImplicit false

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped Pointwise

namespace P2mS26K1

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

end P2mS26K1

namespace P2mS26K1

section Galois

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable {v : HeightOneSpectrum (𝓞 K)} {w : v.Extension (𝓞 L)}
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

end Galois

section Coe

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable {v : HeightOneSpectrum (𝓞 K)} {w : v.Extension (𝓞 L)}

theorem coe_eq_algebraMap (l : L) : (l : w.1.adicCompletion L) = algebraMap L (w.1.adicCompletion L) l := by
  rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
  rfl

theorem algebraMap_algebraMap (k : K) :
    algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (algebraMap K (v.adicCompletion K) k)
      = algebraMap L (w.1.adicCompletion L) (algebraMap K L k) := by
  show w.adicCompletionSemialgHom K L _ = _
  exact (w.adicCompletionSemialgHom K L).commutes k

end Coe

end P2mS26K1
p2m_reactivate "P2MW.S_IsDedekindDomain_HeightOneSpectrum_Extension_finrank_adicCompletion_eq_one_of_pow_eq.P2mS26K1"

theorem solution
    (E M : Type*) [Field E] [NumberField E] [Field M] [NumberField M] [Algebra E M] [IsGalois E M]
    {n : ℕ} (hζ : (primitiveRoots n E).Nonempty) (u : E) (α : M) (hα : α ^ n = algebraMap E M u)
    (hgen : ∀ σ : M ≃ₐ[E] M, σ α = α → σ = 1)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))
    (hb : ∃ b : v.adicCompletion E, algebraMap E (v.adicCompletion E) u = b ^ n)
    (w : v.Extension (NumberField.RingOfIntegers M)) :
    Module.finrank (v.adicCompletion E) (w.1.adicCompletion M) = 1 := by
  classical
  obtain ⟨ζ, hζ⟩ := hζ
  have hn0 : 0 < n := by
    by_contra h
    obtain rfl : n = 0 := by omega
    rw [primitiveRoots_zero] at hζ
    exact absurd hζ (Finset.notMem_empty ζ)
  haveI : NeZero n := ⟨hn0.ne'⟩
  have hprim : IsPrimitiveRoot ζ n := (mem_primitiveRoots hn0).mp hζ
  rw [P2mS26K1.finrank_eq_card_Dec (K := E) (L := M) (v := v) (w := w), Subgroup.card_eq_one, eq_bot_iff]
  intro τ hτ
  rw [Subgroup.mem_bot]
  apply hgen
  by_cases hu0 : u = 0
  ·
    subst hu0
    rw [map_zero, pow_eq_zero_iff hn0.ne'] at hα
    rw [hα, map_zero]

  obtain ⟨b, hb⟩ := hb
  let ι := algebraMap (v.adicCompletion E) (w.1.adicCompletion M)
  let j := algebraMap M (w.1.adicCompletion M)
  have hτb : P2mS26K1.extAut hτ (ι b) = ι b := P2mS26K1.extAut_algebraMap hτ b
  have hιu : ι (algebraMap E (v.adicCompletion E) u) = j (algebraMap E M u) :=
    P2mS26K1.algebraMap_algebraMap (K := E) (L := M) (v := v) (w := w) u
  have hαn : (j α) ^ n = (ι b) ^ n := by
    rw [← map_pow, hα, ← hιu, hb, map_pow]
  have hb0 : ι b ≠ 0 := by
    intro h
    have h1 : j α ^ n = 0 := by rw [hαn, h, zero_pow hn0.ne']
    have hα0 : α = 0 := (map_eq_zero j).mp ((pow_eq_zero_iff hn0.ne').mp h1)
    apply hu0
    rw [hα0, zero_pow hn0.ne', eq_comm, map_eq_zero] at hα
    exact hα

  let ζw : w.1.adicCompletion M := j (algebraMap E M ζ)
  have hprimw : IsPrimitiveRoot ζw n :=
    hprim.map_of_injective (f := j.comp (algebraMap E M)) (j.comp (algebraMap E M)).injective
  have hq : (j α / ι b) ^ n = 1 := by
    rw [div_pow, hαn, div_self (pow_ne_zero n hb0)]
  obtain ⟨i, -, hi⟩ := hprimw.eq_pow_of_pow_eq_one hq
  have hαeq : j α = ζw ^ i * ι b := by
    rw [hi, div_mul_cancel₀ _ hb0]

  have hτζ : P2mS26K1.extAut hτ ζw = ζw := by
    show P2mS26K1.extAut hτ (j (algebraMap E M ζ)) = j (algebraMap E M ζ)
    rw [← P2mS26K1.coe_eq_algebraMap, P2mS26K1.extAut_coe_field hτ, AlgEquiv.commutes]
  have hfix : P2mS26K1.extAut hτ (j α) = j α := by
    rw [hαeq, map_mul, map_pow, hτζ, hτb]
  rw [← P2mS26K1.coe_eq_algebraMap, P2mS26K1.extAut_coe_field hτ, P2mS26K1.coe_eq_algebraMap] at hfix
  exact j.injective hfix

end S_IsDedekindDomain_HeightOneSpectrum_Extension_finrank_adicCompletion_eq_one_of_pow_eq
end P2MW
export P2MW.S_IsDedekindDomain_HeightOneSpectrum_Extension_finrank_adicCompletion_eq_one_of_pow_eq (solution)
