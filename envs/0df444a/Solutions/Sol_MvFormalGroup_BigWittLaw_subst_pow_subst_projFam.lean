-- Prove2me | solution 1 for MvFormalGroup.BigWittLaw.subst_pow_subst_projFam
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/a88065e1-4488-52be-9aa1-d13ef048e093

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_BigWittLaw
import Definitions.Def_MvFormalGroup_BigWittFrobenius
import Definitions.Def_MvFormalGroup_ArtinHasse
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_BigWittLaw_subst_pow_subst_projFam

set_option autoImplicit false

universe u

noncomputable section

namespace Ws28K

open MvPowerSeries MvFormalGroup.BigWittLaw

variable (R : Type u) [CommRing R]

theorem hasSubst_omega :
    MvPowerSeries.HasSubst (fun m : ℕ => (PowerSeries.X : PowerSeries R) ^ (m + 1)) := by
  classical
  refine ⟨fun m => ?_, fun d => ?_⟩
  · have h0 : MvPowerSeries.constantCoeff ((PowerSeries.X : PowerSeries R) ^ (m + 1)) = 0 := by
      rw [map_pow]
      show (MvPowerSeries.constantCoeff (MvPowerSeries.X () : MvPowerSeries Unit R)) ^ (m + 1) = 0
      rw [MvPowerSeries.constantCoeff_X, zero_pow (Nat.succ_ne_zero m)]
    rw [h0]
    exact IsNilpotent.zero
  · refine (Set.finite_singleton (d () - 1)).subset fun m hm => ?_
    have h : MvPowerSeries.coeff d ((PowerSeries.X : PowerSeries R) ^ (m + 1)) ≠ 0 := hm
    have h' : MvPowerSeries.coeff d ((MvPowerSeries.X () : MvPowerSeries Unit R) ^ (m + 1)) ≠ 0 := h
    rw [MvPowerSeries.coeff_X_pow] at h'
    split_ifs at h' with hd
    · show m = d () - 1
      rw [hd, Finsupp.single_eq_same]
      omega
    · exact absurd rfl h'

theorem aeval_int_eq {A : Type*} [CommRing A] {inst : Algebra ℤ A} {σ : Type*} (g : σ → A) (P : MvPolynomial σ ℤ) :
    @MvPolynomial.aeval ℤ A σ _ _ inst g P = MvPolynomial.eval₂ (Int.castRingHom A) g P := by
  rw [MvPolynomial.aeval_def]
  congr 1
  exact RingHom.ext_int _ _

theorem subst_omega_toFam (P : MvPolynomial ℕ ℤ) :
    MvPowerSeries.subst (fun m : ℕ => (PowerSeries.X : PowerSeries R) ^ (m + 1)) (toFam R P) =
      MvPolynomial.eval₂ (Int.castRingHom (PowerSeries R)) (fun m : ℕ => (PowerSeries.X : PowerSeries R) ^ (m + 1)) P := by
  rw [toFam, MvPowerSeries.subst_coe, MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
  congr 1
  exact RingHom.ext_int _ _

theorem k3 (p : ℕ) [hp : Fact p.Prime] (f : MvPowerSeries ℕ R)
    (hf0 : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.subst (fun m : ℕ => (PowerSeries.X : PowerSeries R) ^ (m + 1))
        (MvPowerSeries.subst (projFam R p) f)
      = MvPowerSeries.subst (MvFormalGroup.CartierModule.curveFam R) f := by
  have hp2 : 2 ≤ p := hp.out.two_le
  rw [MvPowerSeries.subst_comp_subst_apply (hasSubst_projFam R hp2) (hasSubst_omega R)]
  congr 1
  funext k
  rw [projFam_apply, subst_omega_toFam]
  have h := aeval_omegaInv_projPoly (PowerSeries.X : PowerSeries R) hp2 k
  rw [aeval_int_eq] at h
  rw [h]
  cases k with
  | zero => rfl
  | succ k => rfl

theorem k1b (n : ℕ) (hn : 0 < n) (G : MvPowerSeries ℕ R)
    (hG0 : MvPowerSeries.constantCoeff G = 0) :
    MvPowerSeries.subst (fun m : ℕ => (PowerSeries.X : PowerSeries R) ^ (m + 1))
        (MvPowerSeries.subst (frobFam R n) G)
      = MvPowerSeries.expand n hn.ne'
          (MvPowerSeries.subst (fun m : ℕ => (PowerSeries.X : PowerSeries R) ^ (m + 1)) G) := by
  rw [MvPowerSeries.subst_comp_subst_apply (hasSubst_frobFam R n) (hasSubst_omega R),
    MvPowerSeries.expand, MvPowerSeries.substAlgHom_apply,
    MvPowerSeries.subst_comp_subst_apply (hasSubst_omega R) (MvPowerSeries.HasSubst.X_pow hn.ne')]
  congr 1
  funext m
  rw [frobFam_apply, subst_omega_toFam]
  have h := aeval_omegaInv_frobPoly (PowerSeries.X : PowerSeries R) hn.ne' m
  rw [aeval_int_eq] at h
  rw [h, MvPowerSeries.subst_pow (MvPowerSeries.HasSubst.X_pow hn.ne')]
  show (PowerSeries.X : PowerSeries R) ^ (n * (m + 1)) =
    (MvPowerSeries.subst (fun s : Unit => (MvPowerSeries.X s : MvPowerSeries Unit R) ^ n) (MvPowerSeries.X ())) ^ (m + 1)
  rw [MvPowerSeries.subst_X (MvPowerSeries.HasSubst.X_pow hn.ne'), ← pow_mul]
  rfl

end Ws28K

end

theorem solution
    (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] (f : MvPowerSeries ℕ R)
    (hf0 : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.subst (fun m : ℕ => (PowerSeries.X : PowerSeries R) ^ (m + 1))
        (MvPowerSeries.subst (MvFormalGroup.BigWittLaw.projFam R p) f)
      = MvPowerSeries.subst (MvFormalGroup.CartierModule.curveFam R) f :=
  Ws28K.k3 R p f hf0

end S_MvFormalGroup_BigWittLaw_subst_pow_subst_projFam
end P2MW
export P2MW.S_MvFormalGroup_BigWittLaw_subst_pow_subst_projFam (solution)
