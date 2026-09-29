-- Prove2me | solution 1 for LanglandsTunnell.exists_finset_liftTraceSeed_quatH_a_eq_zero_of_orderOf_eq_eight
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/6cd619c3-e3f2-5241-8419-209f2f2d53bc

import Mathlib
import Definitions.Def_LanglandsTunnell_QuatH
import Definitions.Def_LanglandsTunnell_LiftTraceSeed
import Definitions.Def_AutomorphicForm_ViaCompactCuspNotion
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Theorems.Thm_LanglandsTunnell_ExplicitLift_exists_mem_closure_map_red_eq_of_det_ne_zero
import Theorems.Thm_LanglandsTunnell_ExplicitLift_map_red_injOn_closure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_exists_finset_liftTraceSeed_quatH_a_eq_zero_of_orderOf_eq_eight

set_option autoImplicit false
open NumberField IsDedekindDomain AutomorphicForm LanglandsTunnell
open scoped Pointwise

namespace FrobBookkeeping

theorem ringHom_ext_ratInt {T : Type*} [Semiring T] (f g : 𝓞 ℚ →+* T) : f = g := by
  have h : f.comp Rat.ringOfIntegersEquiv.symm.toRingHom = g.comp Rat.ringOfIntegersEquiv.symm.toRingHom :=
    RingHom.ext_int _ _
  have := congrArg (fun φ => φ.comp Rat.ringOfIntegersEquiv.toRingHom) h
  simpa [RingHom.comp_assoc] using this

theorem algebraMap_int_comp_ringOfIntegersEquiv {L : Type*} [Field L] [NumberField L] :
    (algebraMap ℤ (𝓞 L)).comp Rat.ringOfIntegersEquiv.toRingHom = algebraMap (𝓞 ℚ) (𝓞 L) :=
  ringHom_ext_ratInt _ _

theorem under_ratInt_eq_comap_under_int {L : Type*} [Field L] [NumberField L] (Q : Ideal (𝓞 L)) :
    Q.under (𝓞 ℚ) = (Q.under ℤ).comap Rat.ringOfIntegersEquiv.toRingHom := by
  rw [Ideal.under_def, Ideal.under_def, ← algebraMap_int_comp_ringOfIntegersEquiv, ← Ideal.comap_comap]

theorem card_quotient_under_eq {L : Type*} [Field L] [NumberField L] (Q : Ideal (𝓞 L)) :
    Nat.card (𝓞 ℚ ⧸ Q.under (𝓞 ℚ)) = Nat.card (ℤ ⧸ Q.under ℤ) := by
  have hmap : Q.under ℤ = ((Q.under ℤ).comap Rat.ringOfIntegersEquiv.toRingHom).map (Rat.ringOfIntegersEquiv : 𝓞 ℚ →+* ℤ) :=
    (Ideal.map_comap_of_surjective (Rat.ringOfIntegersEquiv : 𝓞 ℚ →+* ℤ) Rat.ringOfIntegersEquiv.surjective _).symm
  rw [under_ratInt_eq_comap_under_int]
  exact Nat.card_congr (Ideal.quotientEquiv ((Q.under ℤ).comap Rat.ringOfIntegersEquiv.toRingHom) (Q.under ℤ)
    Rat.ringOfIntegersEquiv hmap).toEquiv

theorem under_int_eq_iff {L : Type*} [Field L] [NumberField L] (Q Q' : Ideal (𝓞 L)) :
    Q.under ℤ = Q'.under ℤ ↔ Q.under (𝓞 ℚ) = Q'.under (𝓞 ℚ) := by
  constructor
  · intro h; rw [under_ratInt_eq_comap_under_int, under_ratInt_eq_comap_under_int, h]
  · intro h
    have h1 : (Q.under (𝓞 ℚ)).under ℤ = (Q'.under (𝓞 ℚ)).under ℤ := by rw [h]
    rwa [Ideal.under_under, Ideal.under_under] at h1

theorem isArithFrobAt_ratInt_iff_int {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L]
    (σ : L ≃ₐ[ℚ] L) (Q : Ideal (𝓞 L)) : IsArithFrobAt (𝓞 ℚ) σ Q ↔ IsArithFrobAt ℤ σ Q := by
  constructor
  · intro h x
    have hx := h x
    simp only [MulSemiringAction.toAlgHom_apply] at hx ⊢
    rwa [← card_quotient_under_eq]
  · intro h x
    have hx := h x
    simp only [MulSemiringAction.toAlgHom_apply] at hx ⊢
    rwa [card_quotient_under_eq]

theorem mem_inertia_smul_iff {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L]
    (Q : Ideal (𝓞 L)) (τ g : L ≃ₐ[ℚ] L) :
    g ∈ (τ • Q).inertia (L ≃ₐ[ℚ] L) ↔ τ⁻¹ * g * τ ∈ Q.inertia (L ≃ₐ[ℚ] L) := by
  constructor
  · intro h x
    have hx := h (τ • x)
    rw [Submodule.mem_toAddSubgroup] at hx ⊢
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, smul_sub] at hx
    simpa [mul_smul] using hx
  · intro h x
    have hx := h (τ⁻¹ • x)
    rw [Submodule.mem_toAddSubgroup] at hx ⊢
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, smul_sub]
    simpa [mul_smul] using hx

theorem inertia_smul_eq_bot {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L]
    (Q : Ideal (𝓞 L)) (τ : L ≃ₐ[ℚ] L) (h : Q.inertia (L ≃ₐ[ℚ] L) = ⊥) :
    (τ • Q).inertia (L ≃ₐ[ℚ] L) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [mem_inertia_smul_iff, h, Subgroup.mem_bot] at hg
  rw [Subgroup.mem_bot]
  have : g = τ * (τ⁻¹ * g * τ) * τ⁻¹ := by group
  rw [this, hg]; group

theorem inertia_eq_bot_and_isConj_arithFrobAt {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (Q Q' : Ideal (𝓞 L)) [Q.IsMaximal] [hQ' : Q'.IsMaximal] (hunder : Q.under (𝓞 ℚ) = Q'.under (𝓞 ℚ))
    (hunr : Q.inertia (L ≃ₐ[ℚ] L) = ⊥) (σ : L ≃ₐ[ℚ] L) (hσ : IsArithFrobAt (𝓞 ℚ) σ Q)
    [Finite (𝓞 L ⧸ Q')] :
    Q'.inertia (L ≃ₐ[ℚ] L) = ⊥ ∧ IsConj σ (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q') ∧
      IsArithFrobAt (𝓞 ℚ) (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q') Q' := by
  have hZ : IsArithFrobAt ℤ σ Q := (isArithFrobAt_ratInt_iff_int σ Q).mp hσ
  have hunderZ : Q.under ℤ = Q'.under ℤ := (under_int_eq_iff Q Q').mpr hunder
  obtain ⟨τ, hτ⟩ := Algebra.IsInvariant.exists_smul_of_under_eq ℤ (𝓞 L) (L ≃ₐ[ℚ] L) Q Q' hunderZ
  have hunr' : Q'.inertia (L ≃ₐ[ℚ] L) = ⊥ := by rw [hτ]; exact inertia_smul_eq_bot Q τ hunr
  have hconj : IsArithFrobAt ℤ (τ * σ * τ⁻¹) Q' := by rw [hτ]; exact hZ.conj τ
  have hF : IsArithFrobAt ℤ (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q') Q' := IsArithFrobAt.arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q'
  have hmem := hF.mul_inv_mem_inertia hconj
  rw [hunr', Subgroup.mem_bot] at hmem
  have heq : arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q' = τ * σ * τ⁻¹ := mul_inv_eq_one.mp hmem
  refine ⟨hunr', ?_, (isArithFrobAt_ratInt_iff_int _ Q').mpr hF⟩
  rw [heq]
  exact isConj_iff.mpr ⟨τ, rfl⟩

end FrobBookkeeping

section SeedB
open FLT.ExplicitLift LanglandsTunnell.Lift48
namespace Seed8

theorem K48_order8 : ∀ N ∈ K48, pw N 8 = 1 → pw N 4 ≠ 1 →
    det2 N = -1 ∧ pw N 2 ∈ P16 ∧ det2 (pw N 2) = 1 ∧ tr2 (pw N 2) = 0 := by
  decide

theorem red_neg_one : red (-1) = -1 := by rw [map_neg, map_one]

abbrev Mat3 : Type := Matrix (Fin 2) (Fin 2) (ZMod 3)

theorem map_red_pow (N : Mat) (n : ℕ) : (N ^ n).map red = (N.map red) ^ n := by
  have h : ∀ A : Mat, A.map red = red.mapMatrix A := fun A => rfl
  simp only [h, map_pow]

theorem map_red_mul (A B : Mat) : (A * B).map red = A.map red * B.map red := by
  have h : ∀ A : Mat, A.map red = red.mapMatrix A := fun A => rfl
  simp only [h, map_mul]

theorem map_red_one : (1 : Mat).map red = 1 := by
  have h : ∀ A : Mat, A.map red = red.mapMatrix A := fun A => rfl
  simp only [h, map_one]

theorem exists_K48_map_red_eq (g : GL (Fin 2) (ZMod 3)) : ∃ N ∈ K48, N.map red = (g : Mat3) := by
  have hdet : (g : Mat3).det ≠ 0 := by
    have h := (Matrix.isUnit_iff_isUnit_det (g : Mat3)).mp g.isUnit
    exact h.ne_zero
  obtain ⟨N, hN, hNg⟩ := LanglandsTunnell.ExplicitLift.exists_mem_closure_map_red_eq_of_det_ne_zero (g : Mat3) hdet
  exact ⟨N, (mem_closure_iff_mem_K48 N).1 hN, hNg⟩

theorem K48_mem_closure {N : Mat} (hN : N ∈ K48) : N ∈ Submonoid.closure ({Slift, Tlift} : Set Mat) :=
  (mem_closure_iff_mem_K48 N).2 hN

theorem lift_order8 (g : GL (Fin 2) (ZMod 3)) (hg : orderOf g = 8) (N : Mat) (hN : N ∈ K48)
    (hNg : N.map red = (g : Mat3)) : pw N 8 = 1 ∧ pw N 4 ≠ 1 := by
  have hinj := LanglandsTunnell.ExplicitLift.map_red_injOn_closure
  have hcl := K48_mem_closure hN
  constructor
  · rw [pw_eq_pow]
    apply hinj (pow_mem hcl 8) (K48_mem_closure one_mem_K48)
    show (N ^ 8).map red = (1 : Mat).map red
    rw [map_red_pow, hNg, map_red_one, ← Units.val_pow_eq_pow_val, ← hg, pow_orderOf_eq_one, Units.val_one]
  · rw [pw_eq_pow]
    intro h4
    have h : (g : Mat3) ^ 4 = 1 := by rw [← hNg, ← map_red_pow, h4, map_red_one]
    rw [← Units.val_pow_eq_pow_val, Units.val_eq_one] at h
    have := pow_ne_one_of_lt_orderOf (x := g) (n := 4) (by norm_num) (by rw [hg]; norm_num)
    exact this h

theorem det_eq_neg_one_of_orderOf_eq_eight (g : GL (Fin 2) (ZMod 3)) (hg : orderOf g = 8) :
    (g : Mat3).det = -1 := by
  obtain ⟨N, hN, hNg⟩ := exists_K48_map_red_eq g
  obtain ⟨h8, h4⟩ := lift_order8 g hg N hN hNg
  have hdet := (K48_order8 N hN h8 h4).1
  rw [det2_eq_det] at hdet
  rw [← hNg]
  show (red.mapMatrix N).det = -1
  rw [← RingHom.map_det, hdet, red_neg_one]

theorem exists_P16_map_red_eq_sq (g : GL (Fin 2) (ZMod 3)) (hg : orderOf g = 8) :
    ∃ M ∈ P16, M.map red = ((g ^ 2 : GL (Fin 2) (ZMod 3)) : Mat3) ∧ ((g ^ 2 : GL (Fin 2) (ZMod 3)) : Mat3).det = 1 := by
  obtain ⟨N, hN, hNg⟩ := exists_K48_map_red_eq g
  obtain ⟨h8, h4⟩ := lift_order8 g hg N hN hNg
  obtain ⟨-, hP, hdet, -⟩ := K48_order8 N hN h8 h4
  refine ⟨pw N 2, hP, ?_, ?_⟩
  · rw [pw_eq_pow, map_red_pow, hNg, Units.val_pow_eq_pow_val]
  · rw [det2_eq_det, pw_eq_pow] at hdet
    rw [Units.val_pow_eq_pow_val, ← hNg, ← map_red_pow]
    show (red.mapMatrix (N ^ 2)).det = 1
    rw [← RingHom.map_det, hdet, map_one]

theorem trace_eq_zero_and_det_eq_one (g : GL (Fin 2) (ZMod 3)) (hg : orderOf g = 8) (M : Mat)
    (hM : M ∈ Submonoid.closure ({Slift, Tlift} : Set Mat))
    (hMg : M.map red = ((g ^ 2 : GL (Fin 2) (ZMod 3)) : Mat3)) : M.trace = 0 ∧ M.det = 1 := by
  obtain ⟨N, hN, hNg⟩ := exists_K48_map_red_eq g
  obtain ⟨h8, h4⟩ := lift_order8 g hg N hN hNg
  obtain ⟨-, -, hdet, htr⟩ := K48_order8 N hN h8 h4
  have hinj := LanglandsTunnell.ExplicitLift.map_red_injOn_closure
  have hMN : M = N ^ 2 := by
    apply hinj hM (pow_mem (K48_mem_closure hN) 2)
    show M.map red = (N ^ 2).map red
    rw [hMg, map_red_pow, hNg, Units.val_pow_eq_pow_val]
  subst hMN
  rw [pw_eq_pow, tr2_eq_trace] at htr
  rw [pw_eq_pow, det2_eq_det] at hdet
  exact ⟨htr, hdet⟩

end Seed8
end SeedB

theorem solution
    {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    ∃ S' : Finset (HeightOneSpectrum (𝓞 ↥(fixFld (quatH e)))),
      ∀ (v : HeightOneSpectrum (𝓞 ℚ)) (Q : Ideal (𝓞 L)) (σ : L ≃ₐ[ℚ] L),
        Q.IsMaximal → Q.under (𝓞 ℚ) = v.asIdeal → Q.inertia (L ≃ₐ[ℚ] L) = ⊥ → IsArithFrobAt (𝓞 ℚ) σ Q →
        orderOf (e σ) = 8 →
        ∀ w : HeightOneSpectrum (𝓞 ↥(fixFld (quatH e))), w ∉ S' → w.under (𝓞 ℚ) = v →
          (P2.liftTraceSeed e (quatH e)).a w = 0 ∧ (P2.liftTraceSeed e (quatH e)).b w = 1 := by
  classical
  refine ⟨∅, ?_⟩
  intro v Q σ hQmax hQv hunr hσ h8 w _ hwv
  haveI := hQmax

  have hQw_under : (P2.primeOver (quatH e) w).under (𝓞 ℚ) = v.asIdeal := by
    rw [← Ideal.under_under (B := 𝓞 ↥(fixFld (quatH e))), P2.under_primeOver, ← hwv]
    rfl
  obtain ⟨-, hconj, -⟩ := FrobBookkeeping.inertia_eq_bot_and_isConj_arithFrobAt Q (P2.primeOver (quatH e) w)
    (hQv.trans hQw_under.symm) hunr σ hσ

  have hordF : orderOf (e (arithFrobAt ℤ (L ≃ₐ[ℚ] L) (P2.primeOver (quatH e) w))) = 8 := by
    obtain ⟨c, hc⟩ := isConj_iff.mp hconj
    rw [← hc]
    refine (orderOf_injective e.toMonoidHom e.injective _).trans ?_
    refine (orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective σ).trans ?_
    have h := orderOf_injective e.toMonoidHom e.injective σ
    rw [← h]
    exact h8

  have hF1 : arithFrobAt ℤ (L ≃ₐ[ℚ] L) (P2.primeOver (quatH e) w) ∉ quatH e := by
    intro h
    have hdet := (mem_detKer_iff e _).1 (quatH_le_detKer e h)
    rw [Seed8.det_eq_neg_one_of_orderOf_eq_eight _ hordF] at hdet
    exact absurd hdet (by decide)
  have hF2 : arithFrobAt ℤ (L ≃ₐ[ℚ] L) (P2.primeOver (quatH e) w) ^ 2 ∈ quatH e := by
    obtain ⟨M, hM, hMred, hdet⟩ := Seed8.exists_P16_map_red_eq_sq _ hordF
    refine ⟨(mem_sylowH_iff e _).2 ⟨M, hM, by rw [map_pow]; exact hMred⟩, ?_⟩
    show arithFrobAt ℤ (L ≃ₐ[ℚ] L) (P2.primeOver (quatH e) w) ^ 2 ∈ detKer e
    rw [mem_detKer_iff, map_pow]
    exact hdet
  have hrel : P2.relDeg (quatH e) (arithFrobAt ℤ (L ≃ₐ[ℚ] L) (P2.primeOver (quatH e) w)) = 2 := by
    unfold P2.relDeg
    rw [Nat.find_eq_iff]
    refine ⟨⟨by norm_num, hF2⟩, fun n hn hmem => ?_⟩
    obtain ⟨hn0, hnmem⟩ := hmem
    interval_cases n
    · rw [pow_one] at hnmem; exact hF1 hnmem
  have hseed : P2.seedFrob (quatH e) w = arithFrobAt ℤ (L ≃ₐ[ℚ] L) (P2.primeOver (quatH e) w) ^ 2 := by
    unfold P2.seedFrob
    rw [hrel]

  have hlift : P2.liftOf (e (P2.seedFrob (quatH e) w)) ∈ Submonoid.closure
        ({FLT.ExplicitLift.Slift, FLT.ExplicitLift.Tlift} : Set (Matrix (Fin 2) (Fin 2) (ℤ√(-2)))) ∧
      (P2.liftOf (e (P2.seedFrob (quatH e) w))).map FLT.ExplicitLift.red =
        ((e (P2.seedFrob (quatH e) w) : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) := by
    have hdet : ((e (P2.seedFrob (quatH e) w) : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)).det ≠ 0 := by
      have h := (Matrix.isUnit_iff_isUnit_det ((e (P2.seedFrob (quatH e) w) : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3))).mp
        (e (P2.seedFrob (quatH e) w)).isUnit
      exact h.ne_zero
    obtain ⟨N, hN, hNg⟩ := LanglandsTunnell.ExplicitLift.exists_mem_closure_map_red_eq_of_det_ne_zero _ hdet
    exact Classical.epsilon_spec (p := fun M : Matrix (Fin 2) (Fin 2) (ℤ√(-2)) =>
      M ∈ Submonoid.closure ({FLT.ExplicitLift.Slift, FLT.ExplicitLift.Tlift} : Set (Matrix (Fin 2) (Fin 2) (ℤ√(-2)))) ∧
        M.map FLT.ExplicitLift.red = ((e (P2.seedFrob (quatH e) w) : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3))) ⟨N, hN, hNg⟩
  rw [hseed, map_pow] at hlift
  obtain ⟨htr, hdet⟩ := Seed8.trace_eq_zero_and_det_eq_one _ hordF _ hlift.1 hlift.2
  show (P2.liftOf (e (P2.seedFrob (quatH e) w))).trace = 0 ∧ (P2.liftOf (e (P2.seedFrob (quatH e) w))).det = 1
  rw [hseed, map_pow]
  exact ⟨htr, hdet⟩

end S_LanglandsTunnell_exists_finset_liftTraceSeed_quatH_a_eq_zero_of_orderOf_eq_eight
end P2MW
export P2MW.S_LanglandsTunnell_exists_finset_liftTraceSeed_quatH_a_eq_zero_of_orderOf_eq_eight (solution)
