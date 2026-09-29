-- Prove2me | solution 1 for NumberField.exists_subgroup_units_valuationOfNeZero_eq_one_inf_torsion_eq_bot_existsUnique_coset_of_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/2fe07cd4-48f9-58f3-8687-845040aa0c8a

import Mathlib
import Theorems.Thm_NumberField_exists_addSubgroup_discreteTopology_units_log_valuation_sum_eq_neg_sum_log_absNorm_mul
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_finite_residueField_adicCompletionIntegers
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_exists_subgroup_units_valuationOfNeZero_eq_one_inf_torsion_eq_bot_existsUnique_coset_of_isOpen

set_option autoImplicit false

open NumberField IsDedekindDomain

namespace L2TU

open IsDedekindDomain IsLocalRing

theorem finite_quotient_maximalIdeal_pow {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (h : Finite (ResidueField O)) (n : ℕ) : Finite (O ⧸ maximalIdeal O ^ n) := by
  induction n with
  | zero =>
    simp only [pow_zero, Ideal.one_eq_top]
    exact Finite.of_fintype (O ⧸ ⊤)
  | succ n ih =>
    have hle : maximalIdeal O ^ (n + 1) ≤ maximalIdeal O ^ n := Ideal.pow_le_pow_right (by simp)
    replace ih := Finite.of_equiv _ (DoubleQuot.quotQuotEquivQuotOfLE hle).symm.toEquiv
    suffices Finite (Ideal.map (Ideal.Quotient.mk (maximalIdeal O ^ (n + 1))) (maximalIdeal O ^ n)) from
      .of_ideal_quotient (.map (Ideal.Quotient.mk _) (maximalIdeal O ^ n))
    exact @Finite.of_equiv _ _ h
      ((Ideal.quotEquivPowQuotPowSuccEquiv (IsPrincipalIdealRing.principal (maximalIdeal O))
        (IsDiscreteValuationRing.not_a_field _) n).trans
        (Ideal.powQuotPowSuccEquivMapMkPowSuccPow _ n))

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem pow_mem_of_isOpen (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (U : Subgroup (v.adicCompletion K)ˣ) (hU : IsOpen (U : Set (v.adicCompletion K)ˣ)) :
    ∃ N : ℕ, 0 < N ∧ ∀ u : (v.adicCompletion K)ˣ, Valued.v (u : v.adicCompletion K) = 1 → u ^ N ∈ U := by
  classical

  obtain ⟨t, ht, htU⟩ := (Units.isEmbedding_val₀.isInducing.isOpen_iff).mp hU
  have h1t : (1 : v.adicCompletion K) ∈ t := by
    have : (1 : (v.adicCompletion K)ˣ) ∈ (Units.val ⁻¹' t) := by rw [htU]; exact U.one_mem
    simpa using this
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp ht 1 h1t

  haveI : Finite (𝓞 K ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  have hfin : Finite (ResidueField (v.adicCompletionIntegers K)) :=
    IsDedekindDomain.HeightOneSpectrum.finite_residueField_adicCompletionIntegers K v
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers K)
  have hϖmax : maximalIdeal (v.adicCompletionIntegers K) = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  have hϖlt : ‖((ϖ : v.adicCompletionIntegers K) : v.adicCompletion K)‖ < 1 := by
    rw [Valued.toNormedField.norm_lt_one_iff]
    have hnu : ¬ IsUnit ϖ := hϖ.not_isUnit
    exact (Valuation.Integer.not_isUnit_iff_valuation_lt_one).mp hnu
  have hϖnn : 0 ≤ ‖((ϖ : v.adicCompletionIntegers K) : v.adicCompletion K)‖ := norm_nonneg _
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hϖlt

  haveI hfq : Finite (v.adicCompletionIntegers K ⧸ maximalIdeal (v.adicCompletionIntegers K) ^ n) :=
    finite_quotient_maximalIdeal_pow hfin n
  set N : ℕ := Nat.card (v.adicCompletionIntegers K ⧸ maximalIdeal (v.adicCompletionIntegers K) ^ n)ˣ with hN
  refine ⟨N, Nat.card_pos, fun u hu => ?_⟩

  have huO : (u : v.adicCompletion K) ∈ v.adicCompletionIntegers K := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hu]
  have huO' : ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]
  set uO : (v.adicCompletionIntegers K)ˣ :=
    ⟨⟨_, huO⟩, ⟨_, huO'⟩, Subtype.ext (by simp), Subtype.ext (by simp)⟩ with huOdef

  have hpow : (Units.map (Ideal.Quotient.mk (maximalIdeal (v.adicCompletionIntegers K) ^ n)).toMonoidHom uO) ^ N = 1 :=
    pow_card_eq_one'
  have hmem : (uO : v.adicCompletionIntegers K) ^ N - 1 ∈ maximalIdeal (v.adicCompletionIntegers K) ^ n := by
    rw [← Ideal.Quotient.eq, map_pow, map_one]
    exact congrArg Units.val hpow

  rw [hϖmax, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hmem
  obtain ⟨y, hy⟩ := hmem
  have hnorm : ‖((u : v.adicCompletion K)) ^ N - 1‖ < ε := by
    have hcoe : ((u : v.adicCompletion K)) ^ N - 1 = ((y * ϖ ^ n : v.adicCompletionIntegers K) : v.adicCompletion K) := by
      rw [hy]; rfl
    rw [hcoe, Subring.coe_mul, Subring.coe_pow, norm_mul, norm_pow]
    have hy1 : ‖((y : v.adicCompletionIntegers K) : v.adicCompletion K)‖ ≤ 1 := by
      rw [Valued.toNormedField.norm_le_one_iff]; exact y.2
    calc ‖((y : v.adicCompletionIntegers K) : v.adicCompletion K)‖ * ‖((ϖ : v.adicCompletionIntegers K) : v.adicCompletion K)‖ ^ n
        ≤ 1 * ‖((ϖ : v.adicCompletionIntegers K) : v.adicCompletion K)‖ ^ n :=
          mul_le_mul_of_nonneg_right hy1 (pow_nonneg hϖnn n)
      _ < ε := by rw [one_mul]; exact hn
  have hin : ((u ^ N : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ t := by
    apply hball
    rw [Metric.mem_ball, dist_eq_norm, Units.val_pow_eq_pow_val]
    exact hnorm
  have : u ^ N ∈ (Units.val ⁻¹' t : Set (v.adicCompletion K)ˣ) := hin
  rw [htU] at this
  exact this

end L2TU

namespace L2TU

open NumberField IsDedekindDomain

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem exists_frame (K : Type) [Field K] [NumberField K] (T : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ (ι : Type) (_ : Fintype ι) (u : ι → Kˣ),
      (∀ i, ∀ v : HeightOneSpectrum (𝓞 K), v ∉ T → v.valuationOfNeZero (u i) = 1) ∧
      (∀ n : ι → ℤ, (∃ ζ : (𝓞 K)ˣ, ζ ∈ NumberField.Units.torsion K ∧
          ((ζ : 𝓞 K) : K) = ((∏ i, u i ^ n i : Kˣ) : K)) → n = 0) ∧
      (∀ x : Kˣ, (∀ v : HeightOneSpectrum (𝓞 K), v ∉ T → v.valuationOfNeZero x = 1) →
        ∃ ζ : (𝓞 K)ˣ, ζ ∈ NumberField.Units.torsion K ∧ ∃ n : ι → ℤ,
          (x : K) = ((ζ : 𝓞 K) : K) * ((∏ i, u i ^ n i : Kˣ) : K)) := by
  classical
  obtain ⟨Λ, Log, -, hmul, hmem, hdisc, -, hker⟩ :=
    NumberField.exists_addSubgroup_discreteTopology_units_log_valuation_sum_eq_neg_sum_log_absNorm_mul K T

  have hL1 : Log 1 = 0 := by
    have h := hmul 1 1
    rw [mul_one] at h
    have h' : Log 1 + Log 1 = Log 1 + 0 := by rw [add_zero]; exact h.symm
    exact add_left_cancel h'
  let Lm : Kˣ →* Multiplicative ((Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)) :=
    { toFun := fun x => Multiplicative.ofAdd (Log x)
      map_one' := by rw [hL1]; rfl
      map_mul' := fun x y => by rw [hmul]; rfl }
  have hLm : ∀ x, Lm x = Multiplicative.ofAdd (Log x) := fun x => rfl
  have hLzpow : ∀ (x : Kˣ) (k : ℤ), Log (x ^ k) = k • Log x := by
    intro x k
    have h := map_zpow Lm x k
    rw [hLm, hLm, ← ofAdd_zsmul] at h
    exact Multiplicative.ofAdd.injective h
  have hLprod : ∀ {α : Type} (s : Finset α) (g : α → Kˣ), Log (∏ a ∈ s, g a) = ∑ a ∈ s, Log (g a) := by
    intro α s g
    have h := map_prod Lm g s
    simp only [hLm, ← ofAdd_sum] at h
    exact Multiplicative.ofAdd.injective h

  let ιE : ((Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)) →+
      ((Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin T.card → ℝ)) :=
    { toFun := fun γ => (γ.1, fun j => (γ.2 j : ℝ))
      map_zero' := by ext <;> simp
      map_add' := fun a b => by ext <;> simp }
  have hιE : ∀ γ, ιE γ = (γ.1, fun j => (γ.2 j : ℝ)) := fun γ => rfl
  have hιE_inj : Function.Injective ιE := by
    intro a b h
    rw [hιE, hιE, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    refine Prod.ext h1 (funext fun j => ?_)
    exact_mod_cast congrFun h2 j
  let Λ' : Submodule ℤ ((Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin T.card → ℝ)) :=
    (Λ.map ιE).toIntSubmodule
  have hΛ'mem : ∀ y, y ∈ Λ' ↔ ∃ γ ∈ Λ, ιE γ = y := fun y => AddSubgroup.mem_map

  haveI hdisc' : DiscreteTopology ↥Λ' := by
    haveI := hdisc
    have h0 : IsOpen ({0} : Set ↥Λ) := discreteTopology_iff_isOpen_singleton_zero.mp hdisc
    obtain ⟨W, hW, hW0⟩ := isOpen_induced_iff.mp h0
    have h0W : (0 : (Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)) ∈ W := by
      have : (0 : ↥Λ) ∈ (Subtype.val ⁻¹' W) := by rw [hW0]; exact Set.mem_singleton 0
      exact this
    obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.mp hW 0 h0W
    have hsep : ∀ γ ∈ Λ, dist γ 0 < ε → γ = 0 := by
      intro γ hγ hdist
      have : (⟨γ, hγ⟩ : ↥Λ) ∈ (Subtype.val ⁻¹' W) := hεW (Metric.mem_ball.mpr hdist)
      rw [hW0] at this
      exact congrArg Subtype.val (Set.mem_singleton_iff.mp this)
    rw [discreteTopology_iff_isOpen_singleton_zero]
    have hopen : IsOpen {x : ↥Λ' |
        ‖(x : (Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin T.card → ℝ))‖ < min ε 1} :=
      isOpen_lt (continuous_norm.comp continuous_subtype_val) continuous_const
    convert hopen using 1
    ext x
    simp only [Set.mem_singleton_iff, Set.mem_setOf_eq]
    constructor
    · rintro rfl
      simp only [Submodule.coe_zero, norm_zero, lt_min_iff]
      exact ⟨hε, one_pos⟩
    · intro hx
      obtain ⟨γ, hγ, hγx⟩ := (hΛ'mem _).mp x.2
      rw [lt_min_iff, ← hγx, hιE, Prod.norm_def, max_lt_iff, max_lt_iff] at hx
      obtain ⟨⟨h1, -⟩, ⟨-, h2⟩⟩ := hx
      have hγ2 : γ.2 = 0 := by
        funext j
        have hj : ‖(γ.2 j : ℝ)‖ < 1 := lt_of_le_of_lt (norm_le_pi_norm (fun j => (γ.2 j : ℝ)) j) h2
        rw [Real.norm_eq_abs, ← Int.cast_abs] at hj
        have : |γ.2 j| < 1 := by exact_mod_cast hj
        exact Int.abs_lt_one_iff.mp this
      have hγ0 : γ = 0 := by
        apply hsep γ hγ
        rw [Prod.dist_eq, Prod.fst_zero, Prod.snd_zero, hγ2, dist_self, dist_zero_right]
        exact max_lt h1 hε
      apply Subtype.ext
      rw [← hγx, hγ0, map_zero, Submodule.coe_zero]

  let b := Module.Free.chooseBasis ℤ ↥Λ'
  haveI : Finite (Module.Free.ChooseBasisIndex ℤ ↥Λ') := Module.Finite.finite_basis b
  letI : Fintype (Module.Free.ChooseBasisIndex ℤ ↥Λ') := Fintype.ofFinite _
  have hlift : ∀ i, ∃ u : Kˣ, (∀ v : HeightOneSpectrum (𝓞 K), v ∉ T → v.valuationOfNeZero u = 1) ∧
      ιE (Log u) = ((b i : ↥Λ') : _) := by
    intro i
    obtain ⟨γ, hγ, hγb⟩ := (hΛ'mem _).mp (b i).2
    obtain ⟨u, hu, rfl⟩ := (hmem γ).mp hγ
    exact ⟨u, hu, hγb⟩
  choose u hu huL using hlift
  have hT : ∀ n : Module.Free.ChooseBasisIndex ℤ ↥Λ' → ℤ, ∀ v : HeightOneSpectrum (𝓞 K), v ∉ T →
      v.valuationOfNeZero (∏ i, u i ^ n i) = 1 := by
    intro n v hv
    rw [map_prod]
    exact Finset.prod_eq_one fun i _ => by rw [map_zpow, hu i v hv, one_zpow]
  have hLΦ : ∀ n : Module.Free.ChooseBasisIndex ℤ ↥Λ' → ℤ,
      ιE (Log (∏ i, u i ^ n i)) = ∑ i, n i • (((b i : ↥Λ')) : (Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin T.card → ℝ)) := by
    intro n
    rw [hLprod, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hLzpow, map_zsmul, huL]
  have hcoesum : ∀ n : Module.Free.ChooseBasisIndex ℤ ↥Λ' → ℤ,
      (((∑ i, n i • b i : ↥Λ')) : (Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin T.card → ℝ)) =
        ∑ i, n i • (((b i : ↥Λ')) : (Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin T.card → ℝ)) := by
    intro n
    rw [AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.coe_smul]
  refine ⟨Module.Free.ChooseBasisIndex ℤ ↥Λ', inferInstance, u, hu, ?_, ?_⟩
  ·
    rintro n ⟨ζ, hζ, hζeq⟩
    have h0 : Log (∏ i, u i ^ n i) = 0 := (hker _ (hT n)).mpr ⟨ζ, hζ, hζeq⟩
    have h1 : (∑ i, n i • b i : ↥Λ') = 0 := by
      apply Subtype.ext
      rw [hcoesum, ← hLΦ, h0, map_zero, Submodule.coe_zero]
    exact funext (Fintype.linearIndependent_iff.mp b.linearIndependent n h1)
  ·
    intro x hx
    have hxΛ : ιE (Log x) ∈ Λ' := (hΛ'mem _).mpr ⟨Log x, (hmem _).mpr ⟨x, hx, rfl⟩, rfl⟩
    obtain ⟨n, hn⟩ : ∃ n : Module.Free.ChooseBasisIndex ℤ ↥Λ' → ℤ, (∑ i, n i • b i : ↥Λ') = ⟨ιE (Log x), hxΛ⟩ :=
      ⟨fun i => b.repr ⟨ιE (Log x), hxΛ⟩ i, b.sum_repr _⟩
    have hE : ιE (Log x) = ιE (Log (∏ i, u i ^ n i)) := by
      rw [hLΦ, ← hcoesum, hn]
    have hLeq : Log x = Log (∏ i, u i ^ n i) := hιE_inj hE
    have hy : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ T → v.valuationOfNeZero (x * (∏ i, u i ^ n i)⁻¹) = 1 := by
      intro v hv
      rw [map_mul, map_inv, hx v hv, hT n v hv, inv_one, mul_one]
    have hLy : Log (x * (∏ i, u i ^ n i)⁻¹) = 0 := by
      rw [hmul, ← zpow_neg_one, hLzpow, hLeq, neg_one_zsmul, add_neg_cancel]
    obtain ⟨ζ, hζ, hζeq⟩ := (hker _ hy).mp hLy
    refine ⟨ζ, hζ, n, ?_⟩
    rw [hζeq, Units.val_mul, Units.val_inv_eq_inv_val, mul_assoc, inv_mul_cancel₀ (Units.ne_zero _), mul_one]

end L2TU

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
open scoped Classical in
theorem solution
    (K : Type) [Field K] [NumberField K] (T : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ F : Subgroup Kˣ,
      (∀ φ ∈ F, ∀ v : HeightOneSpectrum (𝓞 K), v ∉ T → v.valuationOfNeZero φ = 1) ∧
      (∀ φ ∈ F, (∃ ζ : (𝓞 K)ˣ, ζ ∈ NumberField.Units.torsion K ∧ ((ζ : 𝓞 K) : K) = (φ : K)) → φ = 1) ∧
      (∀ u : Kˣ, (∀ v : HeightOneSpectrum (𝓞 K), v ∉ T → v.valuationOfNeZero u = 1) →
        ∃ ζ : (𝓞 K)ˣ, ζ ∈ NumberField.Units.torsion K ∧ ∃ φ ∈ F, (u : K) = ((ζ : 𝓞 K) : K) * (φ : K)) ∧
      ∀ (f : HeightOneSpectrum (𝓞 K) → ℤ) (S : Finset (HeightOneSpectrum (𝓞 K))), (∀ v ∈ S, v ∉ T) →
        ∀ U : ∀ v : HeightOneSpectrum (𝓞 K), Subgroup (v.adicCompletion K)ˣ,
          (∀ v ∈ S, IsOpen (U v : Set (v.adicCompletion K)ˣ)) →
          ∃ (n : ℕ) (c : Fin n → Kˣ),
            (∀ j, c j ∈ F ∧ ∀ v ∈ T, f v ∣ Multiplicative.toAdd (v.valuationOfNeZero (c j))) ∧
            ∀ φ ∈ F, (∀ v ∈ T, f v ∣ Multiplicative.toAdd (v.valuationOfNeZero φ)) →
              ∃! j : Fin n,
                (∀ v ∈ S, Units.map (algebraMap K (v.adicCompletion K) : K →* v.adicCompletion K) (φ * (c j)⁻¹) ∈ U v) ∧
                ∀ w : {w : InfinitePlace K // w.IsReal}, 0 < (mixedEmbedding K ((φ * (c j)⁻¹ : Kˣ) : K)).1 w := by
  classical
  obtain ⟨ι, hι, u, hu, hfree, hgen⟩ := L2TU.exists_frame K T

  let Φ : Multiplicative (ι → ℤ) →* Kˣ :=
    { toFun := fun n => ∏ i, u i ^ (Multiplicative.toAdd n) i
      map_one' := by simp
      map_mul' := fun a c => by
        show ∏ i, u i ^ (Multiplicative.toAdd (a * c)) i = (∏ i, u i ^ (Multiplicative.toAdd a) i) * ∏ i, u i ^ (Multiplicative.toAdd c) i
        rw [toAdd_mul, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [Pi.add_apply, zpow_add] }
  have hΦ : ∀ n : ι → ℤ, Φ (Multiplicative.ofAdd n) = ∏ i, u i ^ n i := fun n => rfl
  have hΦT : ∀ m : Multiplicative (ι → ℤ), ∀ v : HeightOneSpectrum (𝓞 K), v ∉ T → v.valuationOfNeZero (Φ m) = 1 := by
    intro m v hv
    show v.valuationOfNeZero (∏ i, u i ^ (Multiplicative.toAdd m) i) = 1
    rw [map_prod]
    exact Finset.prod_eq_one fun i _ => by rw [map_zpow, hu i v hv, one_zpow]
  refine ⟨Φ.range, ?_, ?_, ?_, ?_⟩
  · rintro φ ⟨m, rfl⟩ v hv
    exact hΦT m v hv
  · rintro φ ⟨m, rfl⟩ ⟨ζ, hζ, hζeq⟩
    have h := hfree (Multiplicative.toAdd m) ⟨ζ, hζ, by rw [← hΦ]; exact hζeq⟩
    have hm : m = 1 := by
      rw [← ofAdd_toAdd m, h]; rfl
    rw [hm, map_one]
  · intro x hx
    obtain ⟨ζ, hζ, n, hxeq⟩ := hgen x hx
    exact ⟨ζ, hζ, Φ (Multiplicative.ofAdd n), ⟨_, rfl⟩, by rw [hΦ]; exact hxeq⟩
  · intro f S hST U hU

    have hloc : ∀ v : HeightOneSpectrum (𝓞 K), ∃ N : ℕ, 0 < N ∧ (v ∈ S → ∀ w : (v.adicCompletion K)ˣ,
        Valued.v (w : v.adicCompletion K) = 1 → w ^ N ∈ U v) := by
      intro v
      by_cases hv : v ∈ S
      · obtain ⟨N, hN, h⟩ := L2TU.pow_mem_of_isOpen K v (U v) (hU v hv)
        exact ⟨N, hN, fun _ => h⟩
      · exact ⟨1, one_pos, fun h => absurd h hv⟩
    choose Nv hNv hNvU using hloc
    obtain ⟨Ntot, hNtot_def⟩ : ∃ N : ℕ, N = 2 * ∏ v ∈ S, Nv v := ⟨_, rfl⟩
    have hNtot_pos : 0 < Ntot := by
      rw [hNtot_def]; exact Nat.mul_pos two_pos (Finset.prod_pos fun v _ => hNv v)

    let Hc : Subgroup Kˣ :=
      { carrier := {φ | (∀ v ∈ S, Units.map (algebraMap K (v.adicCompletion K) : K →* v.adicCompletion K) φ ∈ U v) ∧
          ∀ w : {w : InfinitePlace K // w.IsReal}, 0 < (mixedEmbedding K ((φ : Kˣ) : K)).1 w}
        mul_mem' := fun {a c} ha hc => by
          refine ⟨fun v hv => ?_, fun w => ?_⟩
          · rw [map_mul]; exact (U v).mul_mem (ha.1 v hv) (hc.1 v hv)
          · rw [Units.val_mul, map_mul, Prod.fst_mul, Pi.mul_apply]; exact mul_pos (ha.2 w) (hc.2 w)
        one_mem' := by
          refine ⟨fun v hv => ?_, fun w => ?_⟩
          · rw [map_one]; exact (U v).one_mem
          · rw [Units.val_one, map_one, Prod.fst_one, Pi.one_apply]; exact one_pos
        inv_mem' := fun {a} ha => by
          refine ⟨fun v hv => ?_, fun w => ?_⟩
          · rw [map_inv]; exact (U v).inv_mem (ha.1 v hv)
          · have h1 : (mixedEmbedding K ((a⁻¹ : Kˣ) : K)).1 w * (mixedEmbedding K ((a : Kˣ) : K)).1 w = 1 := by
              rw [← Pi.mul_apply, ← Prod.fst_mul, ← map_mul, Units.inv_mul, map_one, Prod.fst_one, Pi.one_apply]
            exact (mul_pos_iff_of_pos_right (ha.2 w)).mp (by rw [h1]; exact one_pos) }
    have hHc : ∀ φ : Kˣ, φ ∈ Hc ↔ (∀ v ∈ S, Units.map (algebraMap K (v.adicCompletion K) : K →* v.adicCompletion K) φ ∈ U v) ∧
          ∀ w : {w : InfinitePlace K // w.IsReal}, 0 < (mixedEmbedding K ((φ : Kˣ) : K)).1 w := fun φ => Iff.rfl

    have hne : ∀ (a : Kˣ) (w : {w : InfinitePlace K // w.IsReal}), (mixedEmbedding K ((a : Kˣ) : K)).1 w ≠ 0 := by
      intro a w h0
      have h1 : (mixedEmbedding K ((a⁻¹ : Kˣ) : K)).1 w * (mixedEmbedding K ((a : Kˣ) : K)).1 w = 1 := by
        rw [← Pi.mul_apply, ← Prod.fst_mul, ← map_mul, Units.inv_mul, map_one, Prod.fst_one, Pi.one_apply]
      rw [h0, mul_zero] at h1
      exact zero_ne_one h1

    have hpowHc : ∀ m : Multiplicative (ι → ℤ), (Φ m) ^ Ntot ∈ Hc := by
      intro m
      refine ⟨fun v hv => ?_, fun w => ?_⟩
      · obtain ⟨k, hk⟩ : Nv v ∣ Ntot := by
          rw [hNtot_def]; exact Dvd.dvd.mul_left (Finset.dvd_prod_of_mem Nv hv) 2
        rw [map_pow, hk, pow_mul]
        refine (U v).pow_mem ?_ k
        apply hNvU v hv
        have hval : Valued.v ((algebraMap K (v.adicCompletion K)) ((Φ m : Kˣ) : K)) = v.valuation K ((Φ m : Kˣ) : K) :=
          HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
        rw [Units.coe_map, MonoidHom.coe_coe, hval, ← HeightOneSpectrum.valuationOfNeZero_eq, hΦT m v (hST v hv)]
        rfl
      · rw [Units.val_pow_eq_pow_val, map_pow, Prod.pow_fst, Pi.pow_apply, hNtot_def]
        exact Even.pow_pos (even_two_mul _) (hne _ w)

    let HL : AddSubgroup (ι → ℤ) :=
      { carrier := {n | Φ (Multiplicative.ofAdd n) ∈ Hc}
        add_mem' := fun {a c} ha hc => by
          show Φ (Multiplicative.ofAdd (a + c)) ∈ Hc
          rw [ofAdd_add, map_mul]; exact Hc.mul_mem ha hc
        zero_mem' := by
          show Φ (Multiplicative.ofAdd 0) ∈ Hc
          rw [ofAdd_zero, map_one]; exact Hc.one_mem
        neg_mem' := fun {a} ha => by
          show Φ (Multiplicative.ofAdd (-a)) ∈ Hc
          rw [ofAdd_neg, map_inv]; exact Hc.inv_mem ha }
    have hHL : ∀ n : ι → ℤ, n ∈ HL ↔ Φ (Multiplicative.ofAdd n) ∈ Hc := fun n => Iff.rfl
    have hrange : (nsmulAddMonoidHom (α := ι → ℤ) Ntot).range ≤ HL := by
      rintro _ ⟨n, rfl⟩
      rw [hHL, nsmulAddMonoidHom_apply, ofAdd_nsmul, map_pow]
      exact hpowHc _
    haveI : (nsmulAddMonoidHom (α := ι → ℤ) Ntot).range.FiniteIndex := by
      refine ⟨?_⟩
      rw [AddSubgroup.index_range_nsmul]
      exact pow_ne_zero _ hNtot_pos.ne'
    haveI hHLfi : HL.FiniteIndex := AddSubgroup.finiteIndex_of_le hrange

    let Lf : AddSubgroup (ι → ℤ) :=
      { carrier := {n | ∀ v ∈ T, f v ∣ Multiplicative.toAdd (v.valuationOfNeZero (Φ (Multiplicative.ofAdd n)))}
        add_mem' := fun {a c} ha hc v hv => by
          rw [ofAdd_add, map_mul, map_mul, toAdd_mul]
          exact dvd_add (ha v hv) (hc v hv)
        zero_mem' := fun v hv => by
          rw [ofAdd_zero, map_one, map_one, toAdd_one]; exact dvd_zero _
        neg_mem' := fun {a} ha v hv => by
          rw [ofAdd_neg, map_inv, map_inv, toAdd_inv]; exact (ha v hv).neg_right }
    have hLf : ∀ n : ι → ℤ, n ∈ Lf ↔
        ∀ v ∈ T, f v ∣ Multiplicative.toAdd (v.valuationOfNeZero (Φ (Multiplicative.ofAdd n))) := fun n => Iff.rfl

    haveI : (HL.addSubgroupOf Lf).FiniteIndex := inferInstance
    haveI hQfin : Finite (↥Lf ⧸ HL.addSubgroupOf Lf) := inferInstance
    letI : Fintype (↥Lf ⧸ HL.addSubgroupOf Lf) := Fintype.ofFinite _
    let e : (↥Lf ⧸ HL.addSubgroupOf Lf) ≃ Fin (Fintype.card (↥Lf ⧸ HL.addSubgroupOf Lf)) := Fintype.equivFin _
    let rep : (↥Lf ⧸ HL.addSubgroupOf Lf) → ↥Lf := Quotient.out
    have hrep : ∀ q : ↥Lf ⧸ HL.addSubgroupOf Lf, (QuotientAddGroup.mk (rep q) : ↥Lf ⧸ HL.addSubgroupOf Lf) = q :=
      fun q => QuotientAddGroup.out_eq' q
    have hkey : ∀ a c : ↥Lf, (QuotientAddGroup.mk a : ↥Lf ⧸ HL.addSubgroupOf Lf) = QuotientAddGroup.mk c ↔
        Φ (Multiplicative.ofAdd (a : ι → ℤ)) * (Φ (Multiplicative.ofAdd (c : ι → ℤ)))⁻¹ ∈ Hc := by
      intro a c
      rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_add, AddSubgroup.coe_neg, hHL,
        ofAdd_add, ofAdd_neg, map_mul, map_inv, ← Hc.inv_mem_iff, mul_inv_rev, inv_inv, mul_comm]
    refine ⟨Fintype.card (↥Lf ⧸ HL.addSubgroupOf Lf), fun j => Φ (Multiplicative.ofAdd ((rep (e.symm j) : ι → ℤ))), ?_, ?_⟩
    · intro j
      exact ⟨⟨_, rfl⟩, (rep (e.symm j)).2⟩
    · rintro φ ⟨m, rfl⟩ hdiv
      have hn : Multiplicative.toAdd m ∈ Lf := by
        rw [hLf]; intro v hv; rw [ofAdd_toAdd]; exact hdiv v hv
      refine ⟨e (QuotientAddGroup.mk ⟨Multiplicative.toAdd m, hn⟩), ?_, ?_⟩
      · have h := (hkey ⟨Multiplicative.toAdd m, hn⟩ (rep (e.symm (e (QuotientAddGroup.mk ⟨Multiplicative.toAdd m, hn⟩))))).mp
          (by rw [Equiv.symm_apply_apply, hrep])
        exact (hHc _).mp h
      · rintro j ⟨h1, h2⟩
        have h : (QuotientAddGroup.mk ⟨Multiplicative.toAdd m, hn⟩ : ↥Lf ⧸ HL.addSubgroupOf Lf) =
            QuotientAddGroup.mk (rep (e.symm j)) := by
          rw [hkey]
          show Φ (Multiplicative.ofAdd (Multiplicative.toAdd m)) * _ ∈ Hc
          rw [ofAdd_toAdd]
          exact (hHc _).mpr ⟨h1, h2⟩
        rw [hrep] at h
        rw [h, Equiv.apply_symm_apply]

end S_NumberField_exists_subgroup_units_valuationOfNeZero_eq_one_inf_torsion_eq_bot_existsUnique_coset_of_isOpen
end P2MW
export P2MW.S_NumberField_exists_subgroup_units_valuationOfNeZero_eq_one_inf_torsion_eq_bot_existsUnique_coset_of_isOpen (solution)
