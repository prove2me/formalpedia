-- Prove2me | solution 1 for GlobalTheory.HL.DivisibleGauss.share_and_gauss_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:21:50.523702+00:00
-- url     : https://prove2.me/submissions/a7c49376-df6f-4367-94f4-05a047e14797

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SqNormSumRepsMulIndexLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLocalCharacterSum
import Theorems.Thm_GlobalTheory_HL_DivisibleGauss_card_reps_eq_relIndex
import Theorems.Thm_GlobalTheory_HL_DivisibleGauss_sq_norm_sum_mul_relIndex_le
import Theorems.Thm_GlobalTheory_HL_DivisibleGauss_index_span_mul
import Theorems.Thm_GlobalTheory_HL_DivisibleGauss_index_span_involution
import Theorems.Thm_GlobalTheory_HL_DivisibleGauss_form_add_right
import Theorems.Thm_GlobalTheory_HL_DivisibleGauss_form_smul_left
import Theorems.Thm_GlobalTheory_HL_DivisibleGauss_form_smul_right
import Theorems.Thm_GlobalTheory_HL_DivisibleGauss_form_cj
import Theorems.Thm_GlobalTheory_HL_DivisibleGauss_relIndex_divBy
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_GaussSum_mul_conj_eq
import Theorems.Thm_GlobalTheory_UnramOrder_algebraMap_inj
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



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical ComplexConjugate
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.DivisibleGauss
namespace GlobalTheory.HL.DivisibleGauss
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ ϖ : 𝒪[F], Irreducible ϖ → ∀ (ψ : AddChar F ℂ), (∀ x : F, ‖ψ x‖ = 1) → (∀ x : F, (∀ y : 𝒪[F], ψ (x * y) = 1) ↔ x ∈ 𝒪[F]) → ∀ (UU : Submodule L.O (Fin n → E)), (∀ x ∈ UU, ∀ y ∈ UU, hf L Hm x y ∈ L.O) → ∀ (ρ : ℕ) (e : Fin ρ → Fin n → E), (∀ a, e a ∈ UU) → (∀ a b, hf L Hm (e a) (e b) = if a = b then 1 else 0) → ∀ (π : E) (j N : ℕ), π ∈ L.O → π * L.cj π = algebraMap F E ((ϖ : F) ^ j) → (∃ c ∈ L.O, algebraMap F E ((ϖ : F) ^ N) = π * c) → ∀ (R : Finset (Fin n → E)) (nrm : (Fin n → E) → F), (∀ u, algebraMap F E (nrm u) = hf L Hm u u) → (∀ u ∈ R, u ∈ UU) → (∀ u ∈ UU, ∃! w, w ∈ R ∧ ∃ y ∈ UU, u - w = algebraMap F E ((ϖ : F) ^ N) • y) → ((R.filter fun u => ∀ a, ∃ c ∈ L.O, hf L Hm u (e a) = π * c).card : ℝ) = (R.card : ℝ) * (resQ ϖ : ℝ) ^ (-(j * ρ : ℤ)) ∧ ∀ (i : ℕ), i ≤ N → ∀ (t : F) (u₀ : (𝒪[F])ˣ), t * (ϖ : F) ^ i = ((u₀ : 𝒪[F]) : F) → ‖∑ u ∈ R.filter (fun u => ∀ a, ∃ c ∈ L.O, hf L Hm u (e a) = π * c), ψ (t * nrm u)‖ ≤ (R.card : ℝ) * (resQ ϖ : ℝ) ^ (-(j * ρ : ℤ)) * (resQ ϖ : ℝ) ^ (-(((i - j : ℕ) : ℤ) * ρ)) := by
  intro F _ _ _ _ _ E _ _ _ L n Hm hH ϖ hϖ ψ hψ1 hψ U hU ρ e he hee π j N hπ hππ hN R nrm hnrm hRU hR
  obtain ⟨-, -, hdual, -, hint, hcard, hq, -⟩ := GlobalTheory.UnramOrder.order_facts L ϖ hϖ
  have hinj := GlobalTheory.UnramOrder.algebraMap_inj L
  have hcj : ∀ {x}, x ∈ L.O → L.cj x ∈ L.O := fun hx => GlobalTheory.UnramOrder.cj_mem L hx
  have hO : ∀ c : 𝒪[F], algebraMap F E c ∈ L.O := fun c => (hint c).2 c.2
  have hq0 : 0 < resQ ϖ := by omega
  have hq0' : (0 : ℝ) < resQ ϖ := by exact_mod_cast hq0

  let p : ℕ → L.O := fun k => ⟨algebraMap F E ((ϖ : F) ^ k), hO (ϖ ^ k)⟩
  have hp : ∀ k, (Ideal.span {p k}).toAddSubgroup.index = resQ ϖ ^ (2 * k) := fun k => by
    have hset : {y : L.O | (y : E) = algebraMap F E ((ϖ : F) ^ k)} = {p k} := by
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Subtype.ext_iff, p]
    rw [← hcard k, hset]
    rfl
  let π' : L.O := ⟨π, hπ⟩
  have hϖ0 : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hπu : IsUnit π := by
    have := (IsUnit.mk0 _ (pow_ne_zero j hϖ0)).map (algebraMap F E)
    rw [← hππ] at this
    exact isUnit_of_mul_isUnit_left this
  have hreg : ∀ z, π' * z = 0 → z = 0 := fun z hz =>
    Subtype.ext (hπu.mul_right_eq_zero.1 (congrArg Subtype.val hz))
  have hπi : (Ideal.span {π'}).toAddSubgroup.index = resQ ϖ ^ j := by
    let c : L.O →+* L.O := (L.cj : E →+* E).restrict L.O L.O fun x hx => hcj hx
    have h1 := index_span_mul π' (c π') hreg
    have h2 : π' * c π' = p j := Subtype.ext hππ
    rw [index_span_involution c (fun x => Subtype.ext (L.cj_cj x)), h2, hp, ← sq,
      mul_comm 2 j, pow_mul] at h1
    exact (Nat.pow_left_injective two_ne_zero h1).symm

  let P : AddSubgroup (Fin n → E) :=
    U.toAddSubgroup.map (DistribSMul.toAddMonoidHom _ (algebraMap F E ((ϖ : F) ^ N)))
  have hP : ∀ u, u ∈ P ↔ ∃ y ∈ U, u = algebraMap F E ((ϖ : F) ^ N) • y := fun u =>
    ⟨fun ⟨y, hy, h⟩ => ⟨y, hy, h.symm⟩, fun ⟨y, hy, h⟩ => ⟨y, hy, h.symm⟩⟩
  have hPA : ∀ x : E, (∃ c ∈ L.O, algebraMap F E ((ϖ : F) ^ N) = x * c) →
      P ≤ divBy L Hm U e x := by
    rintro x ⟨c, hc, hx⟩ u hu
    obtain ⟨y, hy, rfl⟩ := (hP u).1 hu
    refine ⟨U.smul_mem (p N) hy, fun a => ⟨c * hf L Hm y (e a), L.O.mul_mem hc (hU y hy _ (he a)), ?_⟩⟩
    rw [form_smul_left, hx, mul_assoc]
  let M := divBy L Hm U e π
  have hPM : P ≤ M := hPA π hN
  have hMU : M ≤ U.toAddSubgroup := fun u hu => hu.1
  have hMi : M.relIndex U.toAddSubgroup = (resQ ϖ ^ j) ^ ρ := by
    rw [← hπi]
    exact relIndex_divBy L Hm U hU e he hee π'
  set R₀ := R.filter fun u => ∀ a, ∃ c ∈ L.O, hf L Hm u (e a) = π * c with hR₀
  have hR₀M : ∀ u ∈ R₀, u ∈ M := fun u hu =>
    ⟨hRU u (Finset.mem_filter.1 hu).1, (Finset.mem_filter.1 hu).2⟩
  have hR' : ∀ u ∈ U.toAddSubgroup, ∃! w, w ∈ R ∧ u - w ∈ P := fun u hu => by
    simpa only [hP] using hR u hu
  have hR₀' : ∀ u ∈ M, ∃! w, w ∈ R₀ ∧ u - w ∈ P := fun u hu => by
    obtain ⟨w, ⟨hw, hw'⟩, huniq⟩ := hR' u hu.1
    have hwM : w ∈ M := by simpa using M.sub_mem hu (hPM hw')
    exact ⟨w, ⟨Finset.mem_filter.2 ⟨hw, hwM.2⟩, hw'⟩,
      fun y hy => huniq y ⟨(Finset.mem_filter.1 hy.1).1, hy.2⟩⟩
  have hshare : (R₀.card : ℝ) = (R.card : ℝ) * (resQ ϖ : ℝ) ^ (-(j * ρ : ℤ)) := by
    have h1 := AddSubgroup.relIndex_mul_relIndex P M U.toAddSubgroup hPM hMU
    rw [hMi, ← card_reps_eq_relIndex M P R₀ hR₀M hR₀',
      ← card_reps_eq_relIndex U.toAddSubgroup P R hRU hR', ← pow_mul] at h1
    rw [zpow_neg, ← div_eq_mul_inv, eq_div_iff (by positivity)]
    exact_mod_cast h1
  refine ⟨hshare, fun i hiN t u₀ ht => ?_⟩
  rw [← hshare]
  set k := i - j with hk
  let Q := divBy L Hm U e (π * algebraMap F E ((ϖ : F) ^ k))
  have hQM : Q ≤ M := fun u hu => ⟨hu.1, fun a => by
    obtain ⟨c, hc, h⟩ := hu.2 a
    exact ⟨_, L.O.mul_mem (p k).2 hc, by rw [h, mul_assoc]⟩⟩
  have hQi : Q.relIndex M = (resQ ϖ ^ (k * ρ)) ^ 2 := by
    have h1 := AddSubgroup.relIndex_mul_relIndex Q M U.toAddSubgroup hQM hMU
    have h2 : Q.relIndex U.toAddSubgroup = _ := relIndex_divBy L Hm U hU e he hee (π' * p k)
    rw [hMi, h2, index_span_mul π' _ hreg, hp, hπi, mul_pow] at h1
    rw [Nat.eq_of_mul_eq_mul_right (by positivity) h1]
    ring
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hiN
  have hPQ : P ≤ Q := by
    refine hPA _ ?_
    rcases le_total i j with hij | hij
    · have : k = 0 := by omega
      simpa only [this, pow_zero, map_one, mul_one] using hN
    · refine ⟨L.cj π * algebraMap F E ((ϖ : F) ^ m), L.O.mul_mem (hcj hπ) (p m).2, ?_⟩
      have : N = j + k + m := by omega
      rw [this, pow_add, pow_add, map_mul, map_mul, ← hππ]
      ring
  have hτ : algebraMap F E t * algebraMap F E ((ϖ : F) ^ i)
      = algebraMap F E ((u₀ : 𝒪[F]) : F) := by rw [← map_mul, ht]
  have key := sq_norm_sum_mul_relIndex_le M P Q hPQ R₀ hR₀M hR₀' (fun u => ψ (t * nrm u))
    (fun u => hψ1 _) ?_ ?_
  · rw [hQi, Nat.cast_pow, ← mul_pow] at key
    have h := (sq_le_sq₀ (by positivity) (by positivity)).1 key
    rw [zpow_neg, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    exact_mod_cast h
  · intro u hu y' hy'
    obtain ⟨y, hy, rfl⟩ := (hP y').1 hy'
    have h2 : algebraMap F E t * algebraMap F E ((ϖ : F) ^ N) ∈ L.O := by
      rw [hm, pow_add, map_mul, ← mul_assoc, hτ]
      exact L.O.mul_mem (hO _) (p m).2
    have h3 : t * (nrm (u + algebraMap F E ((ϖ : F) ^ N) • y) - nrm u) ∈ 𝒪[F] := by
      rw [← hint, map_mul, map_sub, hnrm, hnrm]
      have : algebraMap F E t * (hf L Hm (u + algebraMap F E ((ϖ : F) ^ N) • y)
            (u + algebraMap F E ((ϖ : F) ^ N) • y) - hf L Hm u u)
          = algebraMap F E t * algebraMap F E ((ϖ : F) ^ N) * (hf L Hm u y + hf L Hm y u
            + algebraMap F E ((ϖ : F) ^ N) * hf L Hm y y) := by
        simp only [form_add_left, form_add_right, form_smul_left, form_smul_right,
          AlgEquiv.commutes]
        ring
      rw [this]
      exact L.O.mul_mem h2 (L.O.add_mem (L.O.add_mem (hU _ hu.1 _ hy) (hU _ hy _ hu.1))
        (L.O.mul_mem (p N).2 (hU _ hy _ hy)))
    have h4 := (hψ _).2 h3 1
    have h5 : t * nrm (u + algebraMap F E ((ϖ : F) ^ N) • y) = t * nrm u
        + t * (nrm (u + algebraMap F E ((ϖ : F) ^ N) • y) - nrm u) * ((1 : 𝒪[F]) : F) := by
      push_cast; ring
    show ψ _ = ψ _
    rw [h5, AddChar.map_add_eq_mul, h4, mul_one]
  · intro h hM hh
    obtain ⟨a, ha⟩ := not_forall.1 fun h' => hh ⟨hM.1, h'⟩
    obtain ⟨c, hc, hca⟩ := hM.2 a
    have hij : i = j + k := by
      by_contra hne
      have : k = 0 := by omega
      exact ha ⟨c, hc, by rw [this, pow_zero, map_one, mul_one, hca]⟩
    set z := algebraMap F E (t * (ϖ : F) ^ j) * c with hz
    have h1 : z ∉ L.O := fun h' => ha
      ⟨algebraMap F E ((u₀⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) * z, L.O.mul_mem (hO _) h', by
          have h2 : algebraMap F E ((u₀ : 𝒪[F]) : F)
              * algebraMap F E ((u₀⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) = 1 := by
            rw [← map_mul, ← Subring.coe_mul, Units.mul_inv]; simp
          rw [hij, pow_add, map_mul] at hτ
          rw [hca, hz, map_mul]
          linear_combination (-(π * c)) * h2
            - algebraMap F E ((u₀⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) * (π * c) * hτ⟩
    obtain ⟨b, hb⟩ := not_forall.1 fun h' => h1 (hdual _ h')
    obtain ⟨hb, hb'⟩ := Classical.not_imp.1 hb
    obtain ⟨s, hs⟩ := (L.cj_fix (z * L.cj b + L.cj (z * L.cj b))).1
      (by rw [map_add, L.cj_cj, add_comm])
    have hs' : s ∉ 𝒪[F] := fun h' => hb' ⟨⟨s, h'⟩, hs.symm⟩
    obtain ⟨y, hy⟩ := not_forall.1 fun h' => hs' ((hψ s).1 h')
    have hyb : algebraMap F E y * b ∈ L.O := L.O.mul_mem (hO y) hb
    let v : Fin n → E := (π * (algebraMap F E y * b)) • e a
    have hv : v ∈ M := by
      refine ⟨U.smul_mem (⟨_, L.O.mul_mem hπ hyb⟩ : L.O) (he a), fun a' =>
        ⟨algebraMap F E y * b * hf L Hm (e a) (e a'), L.O.mul_mem hyb (hU _ (he a) _ (he a')), ?_⟩⟩
      rw [form_smul_left, mul_assoc]
    refine ⟨v, hv, ψ (s * y), hy, fun u _ => ?_⟩
    have h2 : t * nrm (u + v + h) - t * nrm (u + v)
        = s * y + (t * nrm (u + h) - t * nrm u) := by
      apply hinj
      have hca' : hf L Hm (e a) h = L.cj π * L.cj c := by
        rw [← form_cj L Hm hH.1, hca, map_mul]
      have h3 : hf L Hm v h + hf L Hm h v = algebraMap F E ((ϖ : F) ^ j)
          * (algebraMap F E y * (b * L.cj c + c * L.cj b)) := by
        simp only [v, form_smul_left, form_smul_right, hca, hca', map_mul, AlgEquiv.commutes,
          ← hππ]
        ring
      simp only [hz, map_mul, AlgEquiv.commutes, L.cj_cj] at hs
      simp only [map_sub, map_add (algebraMap F E), map_mul, hnrm, hs, form_add_left,
        form_add_right]
      linear_combination algebraMap F E t * h3
    show ψ _ * conj (ψ _) = _ * (ψ _ * conj (ψ _))
    rw [GaussSum.mul_conj_eq ψ hψ1, GaussSum.mul_conj_eq ψ hψ1, h2, AddChar.map_add_eq_mul]
end GlobalTheory.HL.DivisibleGauss
