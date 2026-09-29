-- Prove2me | solution 1 for LanglandsTunnell.exists_inertia_eq_bot_isArithFrobAt_orderOf_eq_eight
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/909cdaa8-3238-573e-b091-fcad38a0dc6f

import Mathlib
import Definitions.Def_LanglandsTunnell_QuatH
import Definitions.Def_LanglandsTunnell_LiftTraceSeed
import Definitions.Def_AutomorphicForm_ViaCompactCuspNotion
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_LanglandsTunnell_AnalyticGates
import Theorems.Thm_LanglandsTunnell_towerDirichletDensity_add_of_orderOf_eq_eight
import Theorems.Thm_GL2F3_isConj_pow_three_of_orderOf_eq_eight
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_exists_inertia_eq_bot_isArithFrobAt_orderOf_eq_eight
p2m_attr_erase "instance" "FrobeniusDensity.liesOver_ratBelow"

set_option autoImplicit false
open NumberField IsDedekindDomain AutomorphicForm LanglandsTunnell
open FrobeniusDensity Filter Topology Asymptotics

namespace Cheb8

def M8 : GL (Fin 2) (ZMod 3) :=
  Units.mkOfMulEqOne !![1, 1; 2, 1] !![2, 1; 2, 2] (by decide)

theorem orderOf_M8 : orderOf M8 = 8 := by
  have h := orderOf_eq_prime_pow (x := M8) (p := 2) (n := 2) (by decide) (by decide)
  simpa using h

theorem exists_orderOf_eq_eight {G : Type*} [Group G] (e : G ≃* GL (Fin 2) (ZMod 3)) :
    ∃ σ : G, orderOf σ = 8 ∧ IsConj σ (σ ^ 3) ∧ ∀ τ : G, (IsConj σ τ ∨ IsConj (σ ^ 5) τ) → orderOf (e τ) = 8 := by
  refine ⟨e.symm M8, ?_, ?_, ?_⟩
  · rw [← orderOf_injective e.toMonoidHom e.injective (e.symm M8)]
    simp [orderOf_M8]
  · obtain ⟨c, hc⟩ := isConj_iff.mp (GL2F3.isConj_pow_three_of_orderOf_eq_eight M8 orderOf_M8)
    refine isConj_iff.mpr ⟨e.symm c, ?_⟩
    have := congrArg e.symm hc
    simpa using this
  · intro τ hτ
    have h8 : orderOf (e.symm M8) = 8 := by
      rw [← orderOf_injective e.toMonoidHom e.injective (e.symm M8)]; simp [orderOf_M8]
    have h8' : orderOf ((e.symm M8) ^ 5) = 8 := by
      rw [orderOf_pow' _ (by norm_num), h8]; norm_num
    refine (orderOf_injective e.toMonoidHom e.injective τ).trans ?_
    rcases hτ with h | h
    · obtain ⟨c, rfl⟩ := isConj_iff.mp h
      rw [← h8]
      exact orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective _
    · obtain ⟨c, rfl⟩ := isConj_iff.mp h
      rw [← h8']
      exact orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective _

theorem infinite_setOf_classIndicator {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (σ : L ≃ₐ[ℚ] L) (h8 : orderOf σ = 8) (h3 : IsConj σ (σ ^ 3)) :
    {ℓ : ℕ | classIndicator σ ℓ + classIndicator (σ ^ 5) ℓ ≠ 0}.Infinite := by
  classical
  obtain ⟨-, hO⟩ := LanglandsTunnell.towerDirichletDensity_add_of_orderOf_eq_eight σ h8 h3

  generalize hσ₅ : σ ^ 5 = σ₅ at hO ⊢
  intro hfin

  have hc : 0 < 2 * (Nat.card {τ : L ≃ₐ[ℚ] L | IsConj σ τ} : ℝ) / (Nat.card (L ≃ₐ[ℚ] L) : ℝ) := by
    have h1 : 0 < (Nat.card {τ : L ≃ₐ[ℚ] L | IsConj σ τ} : ℝ) := by
      have : Nonempty {τ : L ≃ₐ[ℚ] L | IsConj σ τ} := ⟨⟨σ, IsConj.refl σ⟩⟩
      exact_mod_cast Nat.card_pos
    have h2 : 0 < (Nat.card (L ≃ₐ[ℚ] L) : ℝ) := by exact_mod_cast Nat.card_pos
    positivity

  have ha0 : ∀ ℓ ∉ hfin.toFinset,
      ((classIndicator σ ℓ : ℝ) + (classIndicator σ₅ ℓ : ℝ)) = 0 := by
    intro ℓ hℓ
    have hz : classIndicator σ ℓ + classIndicator σ₅ ℓ = 0 := by
      by_contra h; exact hℓ (hfin.mem_toFinset.mpr h)
    have h1 : classIndicator σ ℓ = 0 := by omega
    have h2 : classIndicator σ₅ ℓ = 0 := by omega
    rw [h1, h2]; norm_num
  have hale : ∀ ℓ, ((classIndicator σ ℓ : ℝ) + (classIndicator σ₅ ℓ : ℝ)) ≤ 2 := by
    intro ℓ
    have h1 : (classIndicator σ ℓ : ℝ) ≤ 1 := by exact_mod_cast classIndicator_le_one σ ℓ
    have h2 : (classIndicator σ₅ ℓ : ℝ) ≤ 1 := by exact_mod_cast classIndicator_le_one σ₅ ℓ
    linarith
  have ha_nonneg : ∀ ℓ, 0 ≤ ((classIndicator σ ℓ : ℝ) + (classIndicator σ₅ ℓ : ℝ)) :=
    fun ℓ => by positivity

  have hbound : ∀ s : ℝ, 1 < s →
      |∑' ℓ : ℕ, ((classIndicator σ ℓ : ℝ) + (classIndicator σ₅ ℓ : ℝ)) * (ℓ : ℝ) ^ (-s)| ≤
        2 * (hfin.toFinset.card : ℝ) := by
    intro s hs
    rw [tsum_eq_sum (s := hfin.toFinset) (fun ℓ hℓ => by rw [ha0 ℓ hℓ, zero_mul])]
    have hterm : ∀ ℓ ∈ hfin.toFinset,
        0 ≤ ((classIndicator σ ℓ : ℝ) + (classIndicator σ₅ ℓ : ℝ)) * (ℓ : ℝ) ^ (-s) ∧
        ((classIndicator σ ℓ : ℝ) + (classIndicator σ₅ ℓ : ℝ)) * (ℓ : ℝ) ^ (-s) ≤ 2 := by
      intro ℓ _
      have hr0 : 0 ≤ (ℓ : ℝ) ^ (-s) := Real.rpow_nonneg (Nat.cast_nonneg ℓ) _
      have hr1 : (ℓ : ℝ) ^ (-s) ≤ 1 := by
        rcases Nat.eq_zero_or_pos ℓ with h0 | hpos
        · subst h0; rw [Nat.cast_zero, Real.zero_rpow (by linarith)]; exact zero_le_one
        · exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hpos) (by linarith)
      refine ⟨mul_nonneg (ha_nonneg ℓ) hr0, ?_⟩
      calc ((classIndicator σ ℓ : ℝ) + (classIndicator σ₅ ℓ : ℝ)) * (ℓ : ℝ) ^ (-s) ≤ 2 * 1 :=
            mul_le_mul (hale ℓ) hr1 hr0 (by norm_num)
        _ = 2 := by ring
    rw [abs_of_nonneg (Finset.sum_nonneg fun ℓ hℓ => (hterm ℓ hℓ).1)]
    calc ∑ ℓ ∈ hfin.toFinset, ((classIndicator σ ℓ : ℝ) + (classIndicator σ₅ ℓ : ℝ)) * (ℓ : ℝ) ^ (-s)
        ≤ ∑ _ℓ ∈ hfin.toFinset, (2 : ℝ) := Finset.sum_le_sum fun ℓ hℓ => (hterm ℓ hℓ).2
      _ = 2 * (hfin.toFinset.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]; ring

  obtain ⟨C, hC⟩ := hO.bound

  have hsub : Tendsto (fun s : ℝ => s - 1) (𝓝[>] (1 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, eventually_nhdsWithin_of_forall fun s hs => Set.mem_Ioi.mpr (sub_pos.mpr (Set.mem_Ioi.mp hs))⟩
    have h := ((continuous_sub_right (1 : ℝ)).tendsto 1).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 1))
    simpa using h
  have hlog : Tendsto (fun s : ℝ => Real.log (s - 1)) (𝓝[>] (1 : ℝ)) atBot :=
    Real.tendsto_log_nhdsGT_zero.comp hsub
  have hs1ev : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ), 1 < s := eventually_mem_nhdsWithin

  obtain ⟨s, hs1, hsC, hslog⟩ := (hs1ev.and (hC.and (hlog.eventually
    (eventually_lt_atBot (-(|C| + 2 * (hfin.toFinset.card : ℝ) + 1) /
      (2 * (Nat.card {τ : L ≃ₐ[ℚ] L | IsConj σ τ} : ℝ) / (Nat.card (L ≃ₐ[ℚ] L) : ℝ))))))).exists

  simp only [Real.norm_eq_abs, abs_one, mul_one] at hsC
  have hT := hbound s hs1
  have hlt : (2 * (Nat.card {τ : L ≃ₐ[ℚ] L | IsConj σ τ} : ℝ) / (Nat.card (L ≃ₐ[ℚ] L) : ℝ)) *
      Real.log (s - 1) < -(|C| + 2 * (hfin.toFinset.card : ℝ) + 1) := by
    have h := mul_lt_mul_of_pos_left hslog hc
    rwa [mul_div_cancel₀ _ (ne_of_gt hc)] at h

  have habs1 := (abs_le.mp hsC).1
  have habs2 := (abs_le.mp hT).2
  have hC0 : C ≤ |C| := le_abs_self C
  linarith

theorem exists_of_classIndicator_ne_zero {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (g : L ≃ₐ[ℚ] L) (ℓ : ℕ) (h : classIndicator g ℓ ≠ 0) :
    ∃ (_ : ℓ.Prime) (Q : Ideal (𝓞 L)) (_ : Q.IsPrime) (_ : Q.LiesOver (ratPrimeIdeal ℓ))
      (_ : Q.inertia (L ≃ₐ[ℚ] L) = ⊥) (_ : Finite ((𝓞 L) ⧸ Q)),
      IsConj g (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q) := by
  classical
  unfold classIndicator at h
  split_ifs at h with hc
  · obtain ⟨hℓ, Q, hQ, hover, hin, hconj⟩ := hc
    exact ⟨hℓ, Q, hQ, hover, hin, _, hconj⟩
  · exact absurd rfl h

theorem ringHom_ext_ratInt {T : Type*} [Semiring T] (f g : 𝓞 ℚ →+* T) : f = g := by
  have h : f.comp Rat.ringOfIntegersEquiv.symm.toRingHom = g.comp Rat.ringOfIntegersEquiv.symm.toRingHom :=
    RingHom.ext_int _ _
  have := congrArg (fun φ => φ.comp Rat.ringOfIntegersEquiv.toRingHom) h
  simpa [RingHom.comp_assoc] using this

theorem card_quotient_under_eq {L : Type} [Field L] [NumberField L] (Q : Ideal (𝓞 L)) :
    Nat.card (𝓞 ℚ ⧸ Q.under (𝓞 ℚ)) = Nat.card (ℤ ⧸ Q.under ℤ) := by
  set r : 𝓞 ℚ ≃+* ℤ := Rat.ringOfIntegersEquiv with hr
  have hcomp : (algebraMap ℤ (𝓞 L)).comp r.toRingHom = algebraMap (𝓞 ℚ) (𝓞 L) :=
    ringHom_ext_ratInt _ _
  have hunder : Q.under (𝓞 ℚ) = (Q.under ℤ).comap r.toRingHom := by
    rw [Ideal.under_def, Ideal.under_def, ← hcomp, ← Ideal.comap_comap]
  have hmap : Q.under ℤ = ((Q.under ℤ).comap r.toRingHom).map (r : 𝓞 ℚ →+* ℤ) :=
    (Ideal.map_comap_of_surjective (r : 𝓞 ℚ →+* ℤ) r.surjective _).symm
  rw [hunder]
  exact Nat.card_congr (Ideal.quotientEquiv ((Q.under ℤ).comap r.toRingHom) (Q.under ℤ) r hmap).toEquiv

theorem isArithFrobAt_ratInt_of_int {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (σ : L ≃ₐ[ℚ] L) (Q : Ideal (𝓞 L)) (h : IsArithFrobAt ℤ σ Q) : IsArithFrobAt (𝓞 ℚ) σ Q := by
  intro x
  have hx := h x
  simp only [MulSemiringAction.toAlgHom_apply] at hx ⊢
  rwa [card_quotient_under_eq]

theorem core {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    ∃ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S ∧ ∃ (Q : Ideal (𝓞 L)) (σ : L ≃ₐ[ℚ] L),
      Q.IsMaximal ∧ Q.under (𝓞 ℚ) = v.asIdeal ∧ Q.inertia (L ≃ₐ[ℚ] L) = ⊥ ∧ IsArithFrobAt (𝓞 ℚ) σ Q ∧
        orderOf (e σ) = 8 := by
  classical
  obtain ⟨σ₀, h8, h3, hord⟩ := exists_orderOf_eq_eight e

  let bad : Set ℕ := {ℓ | ℓ.Prime ∧ ∃ v ∈ S, ((ℓ : ℕ) : 𝓞 ℚ) ∈ v.asIdeal}
  have hbadfin : bad.Finite := by

    have hsub : ∀ v : HeightOneSpectrum (𝓞 ℚ),
        ({ℓ : ℕ | ℓ.Prime ∧ ((ℓ : ℕ) : 𝓞 ℚ) ∈ v.asIdeal} : Set ℕ).Subsingleton := by
      intro v ℓ ⟨hℓ, hℓv⟩ ℓ' ⟨hℓ', hℓ'v⟩
      by_contra hne
      have hcop : Nat.Coprime ℓ ℓ' := (Nat.coprime_primes hℓ hℓ').mpr hne
      have hcopZ : IsCoprime ((ℓ : ℕ) : 𝓞 ℚ) ((ℓ' : ℕ) : 𝓞 ℚ) := by
        have h := (Nat.isCoprime_iff_coprime.mpr hcop).map (Int.castRingHom (𝓞 ℚ))
        simpa using h
      obtain ⟨a, b, hab⟩ := hcopZ
      have h1 : (1 : 𝓞 ℚ) ∈ v.asIdeal := by
        rw [← hab]; exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ hℓv) (v.asIdeal.mul_mem_left _ hℓ'v)
      exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
    refine ((S.finite_toSet.biUnion fun v _ => (hsub v).finite)).subset ?_
    rintro ℓ ⟨hℓ, v, hvS, hℓv⟩
    exact Set.mem_biUnion hvS ⟨hℓ, hℓv⟩

  obtain ⟨ℓ, hℓgood, hℓbad⟩ := ((infinite_setOf_classIndicator σ₀ h8 h3).diff hbadfin).nonempty

  have hmark : classIndicator σ₀ ℓ ≠ 0 ∨ classIndicator (σ₀ ^ 5) ℓ ≠ 0 := by
    by_contra h
    push Not at h
    exact hℓgood (by rw [h.1, h.2])

  have hunpack : ∃ (_ : ℓ.Prime) (Q : Ideal (𝓞 L)) (_ : Q.IsPrime) (_ : Q.LiesOver (ratPrimeIdeal ℓ))
      (_ : Q.inertia (L ≃ₐ[ℚ] L) = ⊥) (_ : Finite ((𝓞 L) ⧸ Q)),
      IsConj σ₀ (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q) ∨ IsConj (σ₀ ^ 5) (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q) := by
    rcases hmark with h | h
    · obtain ⟨hℓ, Q, hQ, hover, hin, hfin, hconj⟩ := exists_of_classIndicator_ne_zero σ₀ ℓ h
      exact ⟨hℓ, Q, hQ, hover, hin, hfin, Or.inl hconj⟩
    · obtain ⟨hℓ, Q, hQ, hover, hin, hfin, hconj⟩ := exists_of_classIndicator_ne_zero (σ₀ ^ 5) ℓ h
      exact ⟨hℓ, Q, hQ, hover, hin, hfin, Or.inr hconj⟩
  obtain ⟨hℓ, Q, hQ, hover, hin, hfin, hconj⟩ := hunpack
  haveI := hQ
  haveI := hfin

  have hfrob : IsArithFrobAt ℤ (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q) Q := IsArithFrobAt.arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q

  have hQne : Q ≠ ⊥ := ne_bot_of_liesOver_ratPrimeIdeal hℓ
  have hQmax : Q.IsMaximal := hQ.isMaximal hQne
  have hℓQ : ((ℓ : ℕ) : 𝓞 L) ∈ Q := by
    have h1 : ((ℓ : ℤ) : ℤ) ∈ Q.under ℤ := by
      rw [← hover.over]; exact Ideal.mem_span_singleton_self _
    rw [Ideal.mem_comap, map_natCast] at h1
    exact h1
  have hℓunder : ((ℓ : ℕ) : 𝓞 ℚ) ∈ Q.under (𝓞 ℚ) := by
    rw [Ideal.mem_comap, map_natCast]; exact hℓQ
  have hunder_ne : Q.under (𝓞 ℚ) ≠ ⊥ := by
    intro h0
    rw [h0, Ideal.mem_bot] at hℓunder
    exact hℓ.ne_zero (by exact_mod_cast hℓunder)
  let v : HeightOneSpectrum (𝓞 ℚ) := ⟨Q.under (𝓞 ℚ), inferInstance, hunder_ne⟩
  have hvS : v ∉ S := fun hvS => hℓbad ⟨hℓ, v, hvS, hℓunder⟩
  refine ⟨v, hvS, Q, arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q, hQmax, rfl, hin,
    isArithFrobAt_ratInt_of_int _ Q hfrob, hord _ hconj⟩

end Cheb8

theorem solution
    {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    ∃ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S ∧ ∃ (Q : Ideal (𝓞 L)) (σ : L ≃ₐ[ℚ] L),
      Q.IsMaximal ∧ Q.under (𝓞 ℚ) = v.asIdeal ∧ Q.inertia (L ≃ₐ[ℚ] L) = ⊥ ∧ IsArithFrobAt (𝓞 ℚ) σ Q ∧
        orderOf (e σ) = 8 := by
  exact Cheb8.core e S

end S_LanglandsTunnell_exists_inertia_eq_bot_isArithFrobAt_orderOf_eq_eight
end P2MW
export P2MW.S_LanglandsTunnell_exists_inertia_eq_bot_isArithFrobAt_orderOf_eq_eight (solution)
