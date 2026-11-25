-- Prove2me | solution 1 for GlobalTheory.HL.GaussSum.norm_gauss_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:14:00.278804+00:00
-- url     : https://prove2.me/submissions/3228c1f0-fc7e-43da-a8fc-5674ffe45709

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SqNormSumRepsMulIndexLe
import Theorems.Thm_GlobalTheory_HL_GaussSum_sq_norm_sum_reps_mul_index_le
import Theorems.Thm_GlobalTheory_HL_GaussSum_mul_conj_eq
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_UnramOrder_algebraMap_inj
import Theorems.Thm_GlobalTheory_UnramOrder_algebraMap_mem_iff
import Theorems.Thm_GlobalTheory_UnramOrder_cj_mem
import Theorems.Thm_GlobalTheory_UnramOrder_order_facts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical ComplexConjugate
namespace GlobalTheory.HL.GaussSum
private theorem mem_span_algebraMap_pow_iff_exists_mul {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) (ϖ : 𝒪[F]) (j : ℕ)
    (m : L.O) :
    m ∈ Ideal.span {y : L.O | (y : E) = algebraMap F E ((ϖ : F) ^ j)} ↔
      ∃ c ∈ L.O, (m : E) = algebraMap F E ((ϖ : F) ^ j) * c := by
  have he : algebraMap F E ((ϖ : F) ^ j) ∈ L.O :=
    (GlobalTheory.UnramOrder.algebraMap_mem_iff L _).2 (pow_mem ϖ.2 j)
  have hs : {y : L.O | (y : E) = algebraMap F E ((ϖ : F) ^ j)} = {⟨_, he⟩} := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Subtype.ext_iff]
  rw [hs, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, a.2, by simp [mul_comm]⟩
  · rintro ⟨c, hc, h⟩
    exact ⟨⟨c, hc⟩, Subtype.ext (by simp [h, mul_comm])⟩
private theorem exists_addSubgroup_pow_multiples_index_eq_resQ_pow {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E]
    [TopologicalSpace E] (L : LocE F E) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) (d j : ℕ) :
    ∃ P : AddSubgroup (Fin d → L.O),
      (∀ w, w ∈ P ↔ ∀ a, ∃ c ∈ L.O, (w a : E) = algebraMap F E ((ϖ : F) ^ j) * c) ∧
      P.index = resQ ϖ ^ (2 * j * d) := by
  refine ⟨AddSubgroup.pi Set.univ
    (fun _ => (Ideal.span {y : L.O | (y : E) = algebraMap F E ((ϖ : F) ^ j)}).toAddSubgroup),
    ?_, ?_⟩
  · intro w
    simp only [AddSubgroup.mem_pi, Set.mem_univ, forall_const,
      Submodule.mem_toAddSubgroup]
    exact forall_congr' fun a => mem_span_algebraMap_pow_iff_exists_mul L ϖ j (w a)
  · have hI : (Ideal.span {y : L.O | (y : E) = algebraMap F E ((ϖ : F) ^ j)}).toAddSubgroup.index
        = resQ ϖ ^ (2 * j) := (GlobalTheory.UnramOrder.order_facts L ϖ hϖ).2.2.2.2.2.1 j
    rw [AddSubgroup.index_pi, Finset.prod_congr rfl (fun _ _ => hI), Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, ← pow_mul]
private theorem algebraMap_nrm_second_difference_eq_sum {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) {d : ℕ}
    (nrm : (Fin d → E) → F) (hnrm : ∀ u, algebraMap F E (nrm u) = ∑ a, u a * L.cj (u a))
    (W V H : Fin d → E) :
    algebraMap F E (nrm (W + V + H) - nrm (W + V) - nrm (W + H) + nrm W) =
      ∑ a, (V a * L.cj (H a) + H a * L.cj (V a)) := by
  rw [map_add, map_sub, map_sub, hnrm, hnrm, hnrm, hnrm, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Pi.add_apply, map_add]
  ring
private theorem algebraMap_nrm_add_sub_nrm_eq_sum {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) {d : ℕ}
    (nrm : (Fin d → E) → F) (hnrm : ∀ u, algebraMap F E (nrm u) = ∑ a, u a * L.cj (u a))
    (W V : Fin d → E) :
    algebraMap F E (nrm (W + V) - nrm W) =
      ∑ a, (W a * L.cj (V a) + V a * L.cj (W a) + V a * L.cj (V a)) := by
  rw [map_sub, hnrm, hnrm, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Pi.add_apply, map_add]
  ring
end GlobalTheory.HL.GaussSum
end

set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical ComplexConjugate
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.GaussSum
namespace GlobalTheory.HL.GaussSum
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ ϖ : 𝒪[F], Irreducible ϖ → ∀ (ψ : AddChar F ℂ), (∀ x : F, ‖ψ x‖ = 1) → (∀ x : F, (∀ y : 𝒪[F], ψ (x * y) = 1) ↔ x ∈ 𝒪[F]) → ∀ (d i N : ℕ), 1 ≤ i → i ≤ N → ∀ (t : F) (u₀ : (𝒪[F])ˣ), t * (ϖ : F) ^ i = ((u₀ : 𝒪[F]) : F) → ∀ (χ : AddChar (Fin d → E) ℂ), (∀ u, ‖χ u‖ = 1) → (∀ u : Fin d → E, (∀ a, u a ∈ L.O) → χ (algebraMap F E ((ϖ : F) ^ N) • u) = 1) → ∀ (R : Finset (Fin d → E)) (nrm : (Fin d → E) → F), (∀ u, algebraMap F E (nrm u) = ∑ a, u a * L.cj (u a)) → (∀ u ∈ R, ∀ a, u a ∈ L.O) → (∀ u : Fin d → E, (∀ a, u a ∈ L.O) → ∃! w, w ∈ R ∧ ∀ a, ∃ c ∈ L.O, u a - w a = algebraMap F E ((ϖ : F) ^ N) * c) → ‖∑ u ∈ R, ψ (t * nrm u) * χ u‖ ≤ (R.card : ℝ) * (resQ ϖ : ℝ) ^ (-(i * d : ℤ)) := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ ψ hψ hψo d i N hi hiN t u₀ ht χ hχ hχN R nrm hnrm hRO hR
  have hOF := GlobalTheory.UnramOrder.order_facts L ϖ hϖ
  have hInt := hOF.2.1
  have hDual := hOF.2.2.1
  have hAlgMem := hOF.2.2.2.2.1
  have hq2 : 2 ≤ resQ ϖ := hOF.2.2.2.2.2.2.1
  have hinjA : Function.Injective (algebraMap F E) := GlobalTheory.UnramOrder.algebraMap_inj L
  have hcje : ∀ x : F, L.cj (algebraMap F E x) = algebraMap F E x := fun x => L.cj.commutes x
  have he : ∀ x : F, x ∈ 𝒪[F] → algebraMap F E x ∈ L.O := fun x hx => (hAlgMem x).2 hx
  have hψ1 : ∀ x : F, x ∈ 𝒪[F] → ψ x = 1 := fun x hx => by
    simpa using (hψo x).2 hx 1
  obtain ⟨ι, hι⟩ : ∃ ι : (Fin d → L.O) → (Fin d → E), ∀ w a, ι w a = (w a : E) :=
    ⟨fun w a => (w a : E), fun _ _ => rfl⟩
  have hιinj : Function.Injective ι := fun w w' h =>
    funext fun a => Subtype.ext (by rw [← hι, ← hι, h])
  have hιadd : ∀ w w', ι (w + w') = ι w + ι w' := fun w w' =>
    funext fun a => by simp [hι]
  obtain ⟨P, hmemP, -⟩ := exists_addSubgroup_pow_multiples_index_eq_resQ_pow L ϖ hϖ d N
  obtain ⟨Q, hmemQ, hQidx⟩ := exists_addSubgroup_pow_multiples_index_eq_resQ_pow L ϖ hϖ d i
  have hpow : (ϖ : F) ^ N = (ϖ : F) ^ i * (ϖ : F) ^ (N - i) := by
    rw [← pow_add, Nat.add_sub_cancel' hiN]
  have hPQ : P ≤ Q := by
    intro w hw
    rw [hmemQ]
    rw [hmemP] at hw
    intro a
    obtain ⟨c, hc, h⟩ := hw a
    refine ⟨algebraMap F E ((ϖ : F) ^ (N - i)) * c, mul_mem (he _ (pow_mem ϖ.2 _)) hc, ?_⟩
    rw [h, ← mul_assoc, ← map_mul, ← pow_add, Nat.add_sub_cancel' hiN]
  obtain ⟨g, hg⟩ : ∃ g : (Fin d → L.O) → ℂ, ∀ w, g w = ψ (t * nrm (ι w)) * χ (ι w) :=
    ⟨fun w => ψ (t * nrm (ι w)) * χ (ι w), fun _ => rfl⟩
  have hg1 : ∀ w, ‖g w‖ = 1 := fun w => by rw [hg, norm_mul, hψ, hχ, one_mul]
  have hmc : ∀ (a1 a2 : F) (A1 A2 : Fin d → E),
      ψ a1 * χ A1 * conj (ψ a2 * χ A2) = ψ (a1 - a2) * χ (A1 - A2) := by
    intro a1 a2 A1 A2
    rw [map_mul, ← GlobalTheory.HL.GaussSum.mul_conj_eq ψ hψ, ← GlobalTheory.HL.GaussSum.mul_conj_eq χ hχ]
    ring
  have hgP : ∀ w, ∀ p ∈ P, g (w + p) = g w := by
    intro w p hp
    rw [hmemP] at hp
    choose c hc hpc using hp
    have hιp : ι p = algebraMap F E ((ϖ : F) ^ N) • c :=
      funext fun a => by rw [hι, hpc a, Pi.smul_apply, smul_eq_mul]
    have hχp : χ (ι p) = 1 := by rw [hιp]; exact hχN _ hc
    choose τ hτ using fun a =>
      (hInt (ι w a * L.cj (c a))
        (mul_mem (by rw [hι]; exact (w a).2) (GlobalTheory.UnramOrder.cj_mem L (hc a)))).2.1
    choose ν hν using fun a => (hInt (c a) (hc a)).2.2
    obtain ⟨S, hSmem, hdiff⟩ : ∃ S ∈ 𝒪[F], nrm (ι w + ι p) - nrm (ι w) = (ϖ : F) ^ N * S := by
      refine ⟨∑ a, ((τ a : F) + (ϖ : F) ^ N * (ν a : F)),
        sum_mem fun a _ => add_mem (τ a).2 (mul_mem (pow_mem ϖ.2 _) (ν a).2), ?_⟩
      apply hinjA
      rw [algebraMap_nrm_add_sub_nrm_eq_sum L nrm hnrm, map_mul (algebraMap F E), map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_add, map_mul (algebraMap F E), ← hτ a, ← hν a, hιp]
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, hcje, L.cj_cj]
      ring
    have harg : t * nrm (ι w + ι p) =
        t * nrm (ι w) + ((u₀ : 𝒪[F]) : F) * ((ϖ : F) ^ (N - i) * S) := by
      rw [← ht]
      linear_combination t * hdiff + t * S * hpow
    rw [hg, hg, hιadd, harg, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, hχp,
      hψ1 _ (mul_mem (u₀ : 𝒪[F]).2 (mul_mem (pow_mem ϖ.2 _) hSmem))]
    ring
  have hgQ : ∀ h, h ∉ Q → ∃ (v : Fin d → L.O) (c : ℂ), c ≠ 1 ∧
      ∀ w, g (w + v + h) * conj (g (w + v)) = c * (g (w + h) * conj (g w)) := by
    intro h hh
    rw [hmemQ] at hh
    push Not at hh
    obtain ⟨a, ha⟩ := hh
    have hx : algebraMap F E t * (h a : E) ∉ L.O := by
      intro hxO
      have hu : ((u₀ : 𝒪[F]) : F) * (((u₀⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) : F) = 1 :=
        congrArg Subtype.val (Units.mul_inv u₀)
      refine ha (algebraMap F E (((u₀⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) : F) * (algebraMap F E t * (h a : E)))
        (mul_mem (he _ ((u₀⁻¹ : (𝒪[F])ˣ) : 𝒪[F]).2) hxO) ?_
      have h1 : (ϖ : F) ^ i * (((u₀⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) : F) * t = 1 := by
        calc (ϖ : F) ^ i * (((u₀⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) : F) * t
            = (t * (ϖ : F) ^ i) * (((u₀⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) : F) := by ring
          _ = 1 := by rw [ht, hu]
      calc (h a : E) = algebraMap F E ((ϖ : F) ^ i * (((u₀⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) : F) * t) *
            (h a : E) := by rw [h1, map_one, one_mul]
        _ = _ := by rw [map_mul, map_mul]; ring
    have hnd := mt (hDual _) hx
    push Not at hnd
    obtain ⟨b, hb, hbc⟩ := hnd
    obtain ⟨β, hβ⟩ :=
      (hInt ((h a : E) * L.cj b) (mul_mem (h a).2 (GlobalTheory.UnramOrder.cj_mem L hb))).2.1
    have htβ : t * (β : F) ∉ 𝒪[F] := by
      intro hmem
      apply hbc ⟨t * β, hmem⟩
      have e1 : algebraMap F E t * (h a : E) * L.cj b =
          algebraMap F E t * ((h a : E) * L.cj b) := by ring
      show _ = algebraMap F E (t * (β : F))
      rw [e1, map_mul L.cj (algebraMap F E t), hcje, map_mul (algebraMap F E) t, ← hβ]
      ring
    have hy := mt (hψo (t * β)).1 htβ
    push Not at hy
    obtain ⟨y, hy⟩ := hy
    have hyO : algebraMap F E (y : F) * b ∈ L.O := mul_mem (he _ y.2) hb
    obtain ⟨v, hιv⟩ : ∃ v : Fin d → L.O,
        ∀ a', ι v a' = if a' = a then algebraMap F E (y : F) * b else 0 := by
      refine ⟨Pi.single a ⟨_, hyO⟩, fun a' => ?_⟩
      rw [hι]
      by_cases h' : a' = a <;> simp [h']
    refine ⟨v, ψ (t * β * y), hy, fun w => ?_⟩
    have hid : nrm (ι w + ι v + ι h) - nrm (ι w + ι v) - nrm (ι w + ι h) + nrm (ι w) =
        (β : F) * y := by
      apply hinjA
      rw [algebraMap_nrm_second_difference_eq_sum L nrm hnrm, Finset.sum_eq_single a]
      · rw [hιv, if_pos rfl, hι h a, map_mul (algebraMap F E) (β : F) (y : F), ← hβ]
        simp only [map_mul, hcje, L.cj_cj]
        ring
      · intro a' _ h'
        rw [hιv, if_neg h']
        simp
      · intro h'
        exact absurd (Finset.mem_univ a) h'
    rw [hg, hg, hg, hg]
    simp only [hιadd]
    rw [hmc, hmc]
    simp only [add_sub_cancel_left]
    rw [← mul_assoc, ← AddChar.map_add_eq_mul]
    congr 2
    linear_combination t * hid
  have hsum : ∑ w ∈ R.preimage ι hιinj.injOn, g w = ∑ u ∈ R, ψ (t * nrm u) * χ u := by
    simp only [hg]
    exact Finset.sum_preimage ι R hιinj.injOn (fun u => ψ (t * nrm u) * χ u)
      (fun u hu hnot => absurd ⟨fun a => ⟨u a, hRO u hu a⟩, funext fun a => hι _ a⟩ hnot)
  have hcard : (R.preimage ι hιinj.injOn).card = R.card := by
    have := Finset.sum_preimage ι R hιinj.injOn (fun _ => (1 : ℕ))
      (fun u hu hnot => absurd ⟨fun a => ⟨u a, hRO u hu a⟩, funext fun a => hι _ a⟩ hnot)
    simpa using this
  have hR' : ∀ w, ∃! w', w' ∈ R.preimage ι hιinj.injOn ∧ w - w' ∈ P := by
    intro w
    obtain ⟨u0, ⟨hu0R, hu0⟩, huniq⟩ := hR (ι w) (fun a => by rw [hι]; exact (w a).2)
    have hu0O := hRO u0 hu0R
    have hw0 : ι (fun a => ⟨u0 a, hu0O a⟩) = u0 := funext fun a => hι _ a
    refine ⟨fun a => ⟨u0 a, hu0O a⟩, ⟨?_, ?_⟩, ?_⟩
    · rw [Finset.mem_preimage, hw0]
      exact hu0R
    · rw [hmemP]
      intro a
      obtain ⟨c, hc, h⟩ := hu0 a
      exact ⟨c, hc, by rw [← h, hι]; rfl⟩
    · rintro w' ⟨hw'R, hw'P⟩
      rw [Finset.mem_preimage] at hw'R
      rw [hmemP] at hw'P
      have hw' : ι w' = u0 := huniq (ι w') ⟨hw'R, fun a => by
        obtain ⟨c, hc, h⟩ := hw'P a
        exact ⟨c, hc, by rw [← h, hι, hι]; rfl⟩⟩
      funext a
      exact Subtype.ext ((hι w' a).symm.trans (congrFun hw' a))
  have key := GlobalTheory.HL.GaussSum.sq_norm_sum_reps_mul_index_le P Q hPQ
    (R.preimage ι hιinj.injOn) hR' g hg1 hgP hgQ
  rw [hsum, hcard, hQidx] at key
  have hq : (0 : ℝ) < resQ ϖ := by exact_mod_cast (by omega : 0 < resQ ϖ)
  have hXpos : (0 : ℝ) < (resQ ϖ : ℝ) ^ (i * d) := pow_pos hq _
  have hzp : (resQ ϖ : ℝ) ^ (-(i * d : ℤ)) = ((resQ ϖ : ℝ) ^ (i * d))⁻¹ := by
    rw [zpow_neg, show ((i : ℤ) * d) = ((i * d : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  rw [hzp, ← div_eq_mul_inv, le_div_iff₀ hXpos]
  have hsq : ((resQ ϖ ^ (2 * i * d) : ℕ) : ℝ) = ((resQ ϖ : ℝ) ^ (i * d)) ^ 2 := by
    push_cast
    rw [← pow_mul]
    congr 1
    ring
  rw [hsq] at key
  have hk : (‖∑ u ∈ R, ψ (t * nrm u) * χ u‖ * (resQ ϖ : ℝ) ^ (i * d)) ^ 2 ≤ (R.card : ℝ) ^ 2 := by
    rw [mul_pow]
    exact key
  nlinarith [norm_nonneg (∑ u ∈ R, ψ (t * nrm u) * χ u), hXpos,
    (Nat.cast_nonneg R.card : (0 : ℝ) ≤ R.card),
    mul_nonneg (norm_nonneg (∑ u ∈ R, ψ (t * nrm u) * χ u)) hXpos.le]
end GlobalTheory.HL.GaussSum
