-- Prove2me | solution 1 for GlobalTheory.CMVal.ValEx.exists_isValChar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:03:21.161123+00:00
-- url     : https://prove2.me/submissions/39a84f87-4d61-4bed-b2e9-75c4897dd20b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsUnitaryCharOfOpenSubgroupAndHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_WithZeroEqOfLeExpIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfVal
import Theorems.Thm_GlobalTheory_CMVal_ValEx_exists_locMap
import Theorems.Thm_GlobalTheory_CMVal_ValEx_val_prime
import Theorems.Thm_GlobalTheory_CMVal_ValEx_val_alg
import Theorems.Thm_GlobalTheory_CMVal_ValEx_exists_locChar
import Theorems.Thm_GlobalTheory_CMVal_ValEx_exists_infChar
import Theorems.Thm_GlobalTheory_CMVal_ValEx_val_bar
import Theorems.Thm_GlobalTheory_CMVal_ValEx_over_bar
import Theorems.Thm_GlobalTheory_CMVal_ValEx_eq_or_eq_bar
import Theorems.Thm_GlobalTheory_CMVal_ValEx_isOfFinOrder_div
import Theorems.Thm_GlobalTheory_CMVal_ValEx_continuous_locU
import Theorems.Thm_GlobalTheory_CMVal_ValEx_continuous_finOf
import Theorems.Thm_GlobalTheory_CMVal_ValEx_continuous_infOf
import Theorems.Thm_GlobalTheory_CMVal_ValEx_mem_unitI
import Theorems.Thm_GlobalTheory_CMVal_ValEx_isOpen_unitI
import Theorems.Thm_GlobalTheory_CMVal_ValEx_locU_of_supp
import Theorems.Thm_GlobalTheory_CMVal_ValEx_finIdele_mem
import Theorems.Thm_GlobalTheory_CMVal_ValEx_expAt_two
import Theorems.Thm_GlobalTheory_CMVal_ValEx_locU_single
import Theorems.Thm_GlobalTheory_CMVal_ValEx_locU_prod
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
import Theorems.Thm_GlobalTheory_CMVal_expAt_zero_iff
import Theorems.Thm_GlobalTheory_CMVal_hasInfRatio_iff
import Theorems.Thm_GlobalTheory_CMVal_infDiag_eq
import Theorems.Thm_GlobalTheory_CMVal_suppAt_single
import Theorems.Thm_GlobalTheory_exists_unitary_char_of_open_subgroup_and_hom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped WithZero
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.ValEx
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.CMVal.ValEx
theorem _root_.solution (E : Type) [Field E] [NumberField E] [IsCMField E] {I : Type} [Fintype I] (φ : I → E →+* ℂ)
    (_hφ : IsCMType φ) (s : ℕ) (κ : I → ℕ) (v : HeightOneSpectrum (OF E)) (hv : IsBaseCond (v.asIdeal ^ 2)) :
    ∃ χ : HChar E, IsValChar φ s κ (v.asIdeal ^ 2) ∅ χ := by
  classical
  obtain ⟨⟨w, w', hne, hw, hw'⟩, -, l, hl, h2, hlv, hd, -⟩ := hv.2.2 v (dvd_pow_self _ two_ne_zero)
  have hbw : bar w ≠ w := fun h => (eq_or_eq_bar hw hw').elim (fun e => hne e.symm) (fun e => hne (e.trans h).symm)
  have hval : ∀ P, Over P v → P.valuation E (l : E) = WithZero.exp (-1 : ℤ) := fun P hP => val_prime hl hd P (by
    rw [← hP, Ideal.mem_comap, map_natCast] at hlv; exact hlv)
  obtain ⟨ψi, hi1, hi2, hi3, hi4⟩ := exists_infChar φ (fun i => (κ i : ℤ) + s)
  let u : Eˣ := Units.mk0 (1 + l) (by exact_mod_cast (by omega : 1 + l ≠ 0))
  obtain ⟨ch, hc1, hc2, hc3, hc4, hc5⟩ := exists_locChar hl h2 w (hval w hw)
    (∏ i, Units.map (φ i).toMonoidHom ^ ((κ i : ℤ) + s))⁻¹ u rfl
  choose c hcc hca hcv using fun P : HeightOneSpectrum (𝓞 E) =>
    exists_locMap (IsCMField.complexConj E).toRingEquiv P (bar P) (val_bar P)
  have hcF : ∀ P (k : Eˣ), (k : E) ∈ maximalRealSubfield E →
      Units.map (c P).toMonoidHom (toLoc (bar P) k) = toLoc P k := fun P k hk =>
    Units.ext ((hca P k).trans (congrArg _ ((IsCMField.complexConj_eq_self_iff E (k : E)).2 hk)))
  let Fx : Subgroup (Af E)ˣ := ⨅ P, ((Units.map (c P).toMonoidHom).comp (locU (bar P))).eqLocus (locU P)
  have hFx : ∀ y, y ∈ Fx ↔ ∀ P, Units.map (c P).toMonoidHom (locU (bar P) y) = locU P y := fun y => Subgroup.mem_iInf
  let ρ : (Af E)ˣ →* (w.adicCompletion E)ˣ := locU w / (Units.map (c w).toMonoidHom).comp (locU (bar w))
  have hρ : ∀ y, ρ y = locU w y / Units.map (c w).toMonoidHom (locU (bar w) y) := fun _ => rfl
  let ψ : Ideles E →* ℂˣ := ψi.comp infOf * ch.comp (ρ.comp finOf)
  have hψ : ∀ x, ψ x = ψi (infOf x) * ch (ρ (finOf x)) := fun _ => rfl
  have hρF : ∀ y ∈ Fx, ρ y = 1 := fun y hy => by rw [hρ, (hFx y).1 hy w, div_self']
  obtain ⟨χ, h1, h3, h4, h5⟩ := exists_unitary_char_of_open_subgroup_and_hom (Ideles E)
    (Eˣ × Fx) unitI isOpen_unitI
    ((Neutral.B1.diagUnits E).coprod ((finIdele E).comp (Subgroup.subtype _))) 1 ψ
    ((hi1.comp continuous_infOf).mul (hc1.comp (((continuous_locU w).div'
      ((Continuous.units_map _ (hcc w)).comp (continuous_locU (bar w)))).comp continuous_finOf)))
    (fun x => by rw [hψ, Units.val_mul, norm_mul, hi2, hc2, one_mul]) (by simp) (by
      rintro ⟨k, y⟩ hy
      have hk : ∀ P : HeightOneSpectrum (𝓞 E), P.valuation E k * Valued.v (locU P y.1 : P.adicCompletion E) = 1 := fun P => by
        rw [← val_alg, ← map_mul]; exact mem_unitI.1 hy P
      have hfin := isOfFinOrder_div k fun P => by
        have e1 := hk P
        have e2 := hk (bar P)
        have e3 : c P (locU (bar P) y.1 : (bar P).adicCompletion E) = locU P y.1 := congrArg Units.val ((hFx _).1 y.2 P)
        rw [← hcv, e3] at e2
        exact (eq_inv_of_mul_eq_one_left e2).trans (eq_inv_of_mul_eq_one_left e1).symm
      have e1 : infOf (((Neutral.B1.diagUnits E).coprod ((finIdele E).comp (Subgroup.subtype _))) (k, y)) =
          Units.map (algebraMap E (InfiniteAdeleRing E)).toMonoidHom k := Units.ext (mul_one _)
      have e2 : finOf (((Neutral.B1.diagUnits E).coprod ((finIdele E).comp (Subgroup.subtype _))) (k, y)) =
          Units.map (algebraMap E (Af E)).toMonoidHom k * y.1 := Units.ext rfl
      have e3 : ρ (Units.map (algebraMap E (Af E)).toMonoidHom k) =
          toLoc w (k / Units.map (IsCMField.complexConj E).toRingEquiv.toMonoidHom k) := by
        rw [hρ, map_div]
        congr 1
        exact Units.ext (hca w k)
      rw [hψ, e1, e2, map_mul, hρF _ y.2, mul_one, e3, hc4 _ hfin]
      rw [MonoidHom.inv_apply, MonoidHom.one_apply, eq_comm, mul_inv_eq_one, MonoidHom.finsetProd_apply]
      apply Units.ext
      rw [hi3, Units.coe_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← IsCMField.complexEmbedding_complexConj]
      simp)
  let X : HChar E := ⟨χ, h1, fun k => by simpa using h5 (k, 1)⟩
  have hloc : ∀ P (x : (P.adicCompletion E)ˣ), Valued.v (x : P.adicCompletion E) = 1 → X.loc P x = ch (ρ (single P x)) := by
    intro P x hx
    have e1 : infOf (finIdele E (single P x)) = 1 := Units.ext rfl
    have e2 : finOf (finIdele E (single P x)) = single P x := Units.ext rfl
    change χ (finIdele E (single P x)) = _
    rw [h4 _ (finIdele_mem (suppAt_single P x) (by rw [single_self, hx])), hψ, e1, e2, map_one, one_mul]
  have hinf : ∀ x : Ideles E, finOf x = 1 → χ x = ψi (infOf x) := fun x hx => by
    rw [h4 _ (mem_unitI.2 fun P => by rw [hx]; exact map_one _), hψ, hx, map_one, map_one, mul_one]
  have hu1 : ∀ P, Over P v → toLoc P u ∈ cong (Valued.v : Valuation (P.adicCompletion E) ℤᵐ⁰) 1 := fun P hP => by
    have e : (toLoc P u : P.adicCompletion E) = 1 + algebraMap E _ (l : E) := by
      change algebraMap E _ (1 + (l : E)) = _
      rw [map_add, map_one]
    refine ⟨?_, ?_⟩ <;> rw [e]
    · refine Valuation.map_one_add_of_lt _ ?_
      rw [val_alg, hval P hP, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
    · rw [add_sub_cancel_left, val_alg, hval P hP]; simp
  refine ⟨X, h3, ⟨fun q k => ?_, fun q k => ?_⟩, (hasInfRatio_iff _ _ _).2 fun k => ?_, fun q P hP => ⟨by simp, fun _ => ?_⟩⟩
  · have hm : ∀ Q, Q ∈ Formalism.L2.Host.aboveF (L := E) (maximalRealSubfield E) q ↔ Over Q q := fun Q => by
      unfold Formalism.L2.Host.aboveF
      rw [Set.Finite.mem_toFinset]
      exact HeightOneSpectrum.ext_iff
    have hy : ∏ P ∈ Formalism.L2.Host.aboveF (L := E) (maximalRealSubfield E) q,
        single P (toLoc P (Formalism.L2.Host.upF (maximalRealSubfield E) k)) ∈ Fx := (hFx _).2 fun Q => by
      rw [locU_prod, locU_prod]
      by_cases hQ : Over Q q
      · rw [if_pos ((hm _).2 hQ), if_pos ((hm _).2 (over_bar hQ))]
        exact hcF Q _ (k : maximalRealSubfield E).2
      · rw [if_neg (fun h => hQ ((hm _).1 h)), if_neg, map_one]
        intro h
        have e : Over (bar Q) (Q.under (OF E)) := over_bar rfl
        exact hQ (Eq.trans (Eq.symm e) ((hm _).1 h))
    have := h5 (1, ⟨_, hy⟩)
    simp only [MonoidHom.coprod_apply, map_one, one_mul, MonoidHom.comp_apply, Subgroup.subtype_apply, map_prod,
      MonoidHom.one_apply] at this
    unfold Formalism.L2.Host.HChar.resFin
    rw [MonoidHom.finsetProd_apply]
    exact this
  · unfold Formalism.L2.Host.HChar.resInf
    rw [MonoidHom.finsetProd_apply]
    refine Finset.prod_eq_one fun t _ => ?_
    refine (hinf _ (Units.ext rfl)).trans (hi4 _ (k : maximalRealSubfield E).2 _ fun t' => ?_)
    by_cases h : t' = t
    · subst h
      exact Or.inr (Pi.mulSingle_eq_same (M := fun w : InfinitePlace E => w.Completion) _ _)
    · exact Or.inl (Pi.mulSingle_eq_of_ne (M := fun w : InfinitePlace E => w.Completion) h _)
  · rw [← hi3]
    change ((χ (infDiag k) : ℂˣ) : ℂ) = _
    rw [infDiag_eq]
    exact congrArg Units.val (hinf _ (Units.ext rfl))
  · by_cases hq : q = v
    · subst hq
      have e : expIn (q.asIdeal ^ 2) q = 2 :=
        multiplicity_pow_self q.ne_bot (fun h => q.isPrime.ne_top (Ideal.isUnit_iff.1 h)) 2
      rw [e]
      rcases eq_or_eq_bar hw hP with rfl | rfl
      · have e2 : ∀ x, ρ (single P x) = x := fun x => by
          rw [hρ, locU_single, locU_of_supp (suppAt_single P x) hbw, map_one, div_one]
        refine expAt_two (fun x h h' => ?_) (fun h => hc5 ?_)
        · rw [hloc P x h, e2]; exact hc3 x ⟨h, h'⟩
        · rw [← e2 (toLoc P u), ← hloc P _ (hu1 P hP).1]; exact h _ (hu1 P hP).1 (hu1 P hP).2
      · have e2 : ∀ x, ρ (single (bar w) x) = (Units.map (c w).toMonoidHom x)⁻¹ := fun x => by
          rw [hρ, locU_single, locU_of_supp (suppAt_single _ x) hbw.symm, one_div]
        refine expAt_two (fun x h h' => ?_) (fun h => hc5 ?_)
        · rw [hloc _ x h, e2, map_inv, inv_eq_one]
          refine hc3 _ ⟨(hcv w _).trans h, ?_⟩
          rw [← hcv w, map_sub, map_one] at h'
          exact h'
        · have := h _ (hu1 _ hP).1 (hu1 _ hP).2
          rwa [hloc _ _ (hu1 _ hP).1, e2, map_inv, inv_eq_one, hcF w u (add_mem (one_mem _) (natCast_mem _ l))] at this
    · have e : expIn (v.asIdeal ^ 2) q = 0 := multiplicity_eq_zero.2 fun h => hq
        (HeightOneSpectrum.ext (v.isMaximal.eq_of_le q.isPrime.ne_top
          (Ideal.dvd_iff_le.1 (q.prime.dvd_of_dvd_pow h))).symm)
      have hn : ∀ Q, Over Q v → Q ≠ P := fun Q hQ h => hq (HeightOneSpectrum.ext (Eq.trans (Eq.symm hP) (h ▸ hQ)))
      rw [e, expAt_zero_iff]
      intro x hx
      rw [hloc P x hx, hρ, locU_of_supp (suppAt_single P x) (hn w hw), locU_of_supp (suppAt_single P x) (hn _ (over_bar hw))]
      simp
end GlobalTheory.CMVal.ValEx
