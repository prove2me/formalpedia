-- Prove2me | solution 1 for MvFormalGroup.CartierModule.tangent_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/f26f727b-b889-50e3-acad-5675a361b6c2

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_BigWittLaw
import Definitions.Def_MvFormalGroup_ArtinHasse
import Theorems.Thm_MvFormalGroup_ArtinHasse_subst_addFam_fam
import Theorems.Thm_MvFormalGroup_BigWittLaw_exists_hom_subst_curveFam_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_CartierModule_tangent_surjective
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply"

set_option autoImplicit false

noncomputable section

universe u

open MvPowerSeries MvFormalGroup MvFormalGroup.WittLaw

namespace CartierExistenceSol

variable {p : ℕ} [hp : Fact p.Prime] {R : Type u} [CommRing R] {d : ℕ}

structure IsHomToBigWitt (p : ℕ) [Fact p.Prime] (u : ℕ → MvPowerSeries ℕ R) : Prop where
  hasSubst : HasSubst u
  constantCoeff : ∀ n, (u n).constantCoeff = 0
  subst_addFam : ∀ n, subst (WittLaw.addFam p R) (u n) = subst (WittLaw.pairFam u) (BigWittLaw.addFam R n)

variable {Φ : MvFormalGroup d R}

def compose (G : Fin d → MvPowerSeries ℕ R) (hG0 : ∀ j, (G j).constantCoeff = 0)
    (hG : ∀ j, subst (BigWittLaw.addFam R) (G j) =
      subst (Sum.elim
        (fun l => subst (fun m => (X (0, m) : MvPowerSeries (Fin 2 × ℕ) R)) (G l))
        fun l => subst (fun m => (X (1, m) : MvPowerSeries (Fin 2 × ℕ) R)) (G l))
        (Φ.toPowerSeries j))
    {u : ℕ → MvPowerSeries ℕ R} (hu : IsHomToBigWitt p u) : CartierModule p Φ where
  toPowerSeries := fun j => subst u (G j)
  constantCoeff_eq_zero := fun j =>
    constantCoeff_subst_eq_zero hu.hasSubst hu.constantCoeff (hG0 j)
  subst_eq := by
    intro j
    have hA := hasSubst_addFam p R
    have hP := hasSubst_pairFam hu.hasSubst hu.constantCoeff
    have hB := BigWittLaw.hasSubst_addFam R
    show subst (WittLaw.addFam p R) (subst u (G j)) =
      subst (Sum.elim (CartierModule.inBlk 0 fun l => subst u (G l))
        (CartierModule.inBlk 1 fun l => subst u (G l))) (Φ.toPowerSeries j)
    rw [subst_comp_subst_apply hu.hasSubst hA]
    have hfam : (fun n => subst (WittLaw.addFam p R) (u n)) =
        fun n => subst (WittLaw.pairFam u) (BigWittLaw.addFam R n) := funext hu.subst_addFam
    have hG' : subst (BigWittLaw.addFam R) (G j) =
        subst (Sum.elim (CartierModule.inBlk 0 G) (CartierModule.inBlk 1 G)) (Φ.toPowerSeries j) :=
      hG j
    rw [hfam, ← subst_comp_subst_apply hB hP, hG',
      subst_subst_elim Φ (CartierModule.constantCoeff_inBlk 0 hG0)
        (CartierModule.constantCoeff_inBlk 1 hG0) hP]
    congr 1
    funext s
    rcases s with l | l
    · exact WittLaw.subst_pairFam_subst_blk hu.hasSubst hu.constantCoeff 0 (G l)
    · exact WittLaw.subst_pairFam_subst_blk hu.hasSubst hu.constantCoeff 1 (G l)

@[scoped simp] theorem toPowerSeries_compose (G : Fin d → MvPowerSeries ℕ R) (hG0 : ∀ j, (G j).constantCoeff = 0)
    (hG : ∀ j, subst (BigWittLaw.addFam R) (G j) =
      subst (Sum.elim
        (fun l => subst (fun m => (X (0, m) : MvPowerSeries (Fin 2 × ℕ) R)) (G l))
        fun l => subst (fun m => (X (1, m) : MvPowerSeries (Fin 2 × ℕ) R)) (G l))
        (Φ.toPowerSeries j))
    {u : ℕ → MvPowerSeries ℕ R} (hu : IsHomToBigWitt p u) (j : Fin d) :
    (compose G hG0 hG hu).toPowerSeries j = subst u (G j) := rfl

theorem coeff_single_zero_subst {u : ℕ → MvPowerSeries ℕ R} (hu : HasSubst u)
    (hu0 : ∀ n, (u n).constantCoeff = 0)
    (hu1 : ∀ n, coeff (Finsupp.single 0 1) (u n) = if n = 0 then 1 else 0) (f : MvPowerSeries ℕ R) :
    coeff (Finsupp.single 0 1) (subst u f) = coeff (Finsupp.single 0 1) f := by
  classical
  rw [coeff_subst hu, finsum_eq_single _ (Finsupp.single 0 1)]
  · rw [Finsupp.prod_single_index (h := fun s n => (u s) ^ n) (pow_zero (u 0)), pow_one, hu1 0,
      if_pos rfl, smul_eq_mul, mul_one]
  · intro e he
    suffices hz : coeff (Finsupp.single 0 1) (e.prod fun s n => (u s) ^ n) = 0 by
      rw [hz, smul_zero]
    rcases Nat.lt_trichotomy e.degree 1 with hlt | heq | hgt
    · have he0 : e = 0 := (Finsupp.degree_eq_zero_iff e).mp (by omega)
      subst he0
      rw [Finsupp.prod_zero_index, coeff_one, if_neg (Finsupp.single_ne_zero.mpr one_ne_zero)]
    · obtain ⟨a, rfl⟩ : ∃ a, Finsupp.single a 1 = e := by
        have hmem' : e ∈ {d' : ℕ →₀ ℕ | d'.degree = 1} := heq
        rw [← Finsupp.range_single_one] at hmem'
        exact hmem'
      have ha : a ≠ 0 := fun h => he (by rw [h])
      rw [Finsupp.prod_single_index (h := fun s n => (u s) ^ n) (pow_zero (u a)), pow_one, hu1 a,
        if_neg ha]
    · have horder : (((Finsupp.single (0 : ℕ) 1).degree : ℕ) : ℕ∞) <
          (e.prod fun s n => (u s) ^ n).order := by
        refine lt_of_lt_of_le ?_ (le_order_finsuppProd_pow hu0 e)
        rw [Finsupp.degree_single]
        exact_mod_cast hgt
      exact coeff_of_lt_order horder

theorem coeff_one_subst_curveFam (f : MvPowerSeries ℕ R) :
    PowerSeries.coeff 1 (subst (CartierModule.curveFam R) f) = coeff (Finsupp.single 0 1) f := by
  classical
  have hC := CartierModule.hasSubst_curveFam (R := R)
  show MvPowerSeries.coeff (Finsupp.single () 1) (subst (CartierModule.curveFam R) f) = _
  rw [coeff_subst hC]
  have hterm : ∀ e : ℕ →₀ ℕ, e ≠ Finsupp.single 0 1 →
      coeff e f • coeff (Finsupp.single () 1) (e.prod fun n k => CartierModule.curveFam R n ^ k) = 0 := by
    intro e he
    by_cases hsupp : ∃ n ∈ e.support, n ≠ 0
    · obtain ⟨n, hn, hn0⟩ := hsupp
      have hzero : (e.prod fun n k => CartierModule.curveFam R n ^ k) = 0 := by
        rw [Finsupp.prod]
        refine Finset.prod_eq_zero hn ?_
        obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
        show (0 : PowerSeries R) ^ e (m + 1) = 0
        exact zero_pow (Finsupp.mem_support_iff.mp hn)
      rw [hzero, map_zero, smul_zero]
    · push Not at hsupp
      have he0 : e = Finsupp.single 0 (e 0) := by
        ext n
        by_cases hn : n = 0
        · subst hn; simp
        · rw [Finsupp.single_apply, if_neg (Ne.symm hn)]
          by_contra hne
          exact hn (hsupp n (Finsupp.mem_support_iff.mpr hne))
      have hk : e 0 ≠ 1 := fun h1 => he (by rw [he0, h1])
      rw [he0, Finsupp.prod_single_index (by simp)]
      show coeff _ f • coeff (Finsupp.single () 1) ((PowerSeries.X : PowerSeries R) ^ e 0) = 0
      rw [PowerSeries.X, coeff_X_pow, if_neg, smul_zero]
      intro h
      exact hk ((Finsupp.single_injective ()) h).symm
  rw [finsum_eq_single _ (Finsupp.single 0 1) hterm, Finsupp.prod_single_index (by simp)]
  show coeff _ f • coeff (Finsupp.single () 1) ((PowerSeries.X : PowerSeries R) ^ 1) = _
  rw [pow_one, PowerSeries.X, coeff_X, if_pos rfl, smul_eq_mul, mul_one]

theorem tangent_surjective [CharP R p] (Φ : MvFormalGroup d R) [Φ.IsComm] :
    Function.Surjective (CartierModule.tangent : CartierModule p Φ → Fin d → R) := by
  intro v

  obtain ⟨G, hG0, hG, hcurve⟩ := BigWittLaw.exists_hom_subst_curveFam_eq Φ
    (fun j => v j • (PowerSeries.X : PowerSeries R)) (fun j => by simp)

  have hAH : IsHomToBigWitt p (ArtinHasse.fam p R) :=
    ⟨ArtinHasse.hasSubst_fam p R, ArtinHasse.constantCoeff_fam p R, ArtinHasse.subst_addFam_fam p R⟩
  refine ⟨compose G hG0 hG hAH, funext fun j => ?_⟩
  rw [CartierModule.tangent_apply, toPowerSeries_compose,
    coeff_single_zero_subst (ArtinHasse.hasSubst_fam p R) (ArtinHasse.constantCoeff_fam p R)
      (ArtinHasse.coeff_single_zero_fam p R) (G j),
    ← coeff_one_subst_curveFam, hcurve j]
  simp

end CartierExistenceSol
p2m_reactivate "P2MW.S_MvFormalGroup_CartierModule_tangent_surjective.CartierExistenceSol"

theorem solution
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] [CharP R p] {d : ℕ}
    (Φ : MvFormalGroup d R) [Φ.IsComm] :
    Function.Surjective
      (MvFormalGroup.CartierModule.tangent : MvFormalGroup.CartierModule p Φ → Fin d → R) :=
  CartierExistenceSol.tangent_surjective Φ

end
p2m_reactivate "P2MW.S_MvFormalGroup_CartierModule_tangent_surjective.CartierExistenceSol"

end S_MvFormalGroup_CartierModule_tangent_surjective
end P2MW
export P2MW.S_MvFormalGroup_CartierModule_tangent_surjective (solution)
