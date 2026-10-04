-- Prove2me | solution 1 for KKBinPacking.GeometricGrouping.size_le_lin_le_opt_le_lin_add
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-02T13:49:40.715952+00:00
-- url     : https://prove2.me/submissions/ad4a1544-6ebb-4451-9e9b-d7c58d819c46
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_KKBinPacking_GeometricGrouping_size_le_lin
import Theorems.Thm_KKBinPacking_GeometricGrouping_lin_le_opt
import Theorems.Thm_KKBinPacking_GeometricGrouping_opt_le_two_size_add_one
import Theorems.Thm_KKBinPacking_GeometricGrouping_exists_sparse_near_optimal_lp
import Theorems.Thm_KKBinPacking_GeometricGrouping_lp_floor_rounding_certificate
import Definitions.Def_KKBinPacking_GeometricGrouping_Algorithm2

set_option autoImplicit false
open KKBinPacking.Shared KKBinPacking.GeometricGrouping

namespace KKRoundingUpper

/-- Residual after deleting all slots filled in the principal bins. -/
noncomputable def residual (I : Multiset ℝ) (x : Multiset ℝ →₀ ℝ) : Multiset ℝ :=
  I - (principalConfigs x).join

/-- Floor/delete certificate in Lemma 2, FOCS 1982 p.313. No sparsity assumption. -/
def RoundingCertificate (I : Multiset ℝ) (x : Multiset ℝ →₀ ℝ) : Prop :=
  ∃ P : Multiset (Multiset ℝ),
    IsPacking (I - residual I x) P ∧
    P.card ≤ principalCount x ∧
    SIZE (residual I x) ≤ lpCost x - (principalCount x : ℝ) ∧
    (OPT (residual I x) : ℝ) ≤ (x.support.card : ℝ)

lemma exists_optimal_packing (I : Multiset ℝ) (hI : IsInstance I) :
    ∃ P, IsPacking I P ∧ P.card = OPT I := by
  classical
  have hex : {B : ℕ | ∃ P : Multiset (Multiset ℝ), IsPacking I P ∧ P.card = B}.Nonempty := by
    refine ⟨I.card, I.map (fun t => {t}), ⟨?_, ?_⟩, by simp⟩
    · induction I using Multiset.induction_on with
      | empty => simp
      | cons t I ih => simpa using ih (fun s hs => hI s (by simp [hs]))
    · intro b hb
      obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hb
      simpa using (hI t ht).2.le
  exact Nat.sInf_mem hex

lemma opt_le_card_add_opt (I R : Multiset ℝ) (hI : IsInstance I) (hRI : R ≤ I)
    (P : Multiset (Multiset ℝ)) (hP : IsPacking (I - R) P) :
    OPT I ≤ P.card + OPT R := by
  have hR : IsInstance R := fun t ht => hI t (Multiset.mem_of_le hRI ht)
  obtain ⟨Q, hQ, hcQ⟩ := exists_optimal_packing R hR
  apply Nat.sInf_le
  refine ⟨P + Q, ⟨?_, ?_⟩, ?_⟩
  · rw [Multiset.join_add, hP.1, hQ.1, tsub_add_cancel_of_le hRI]
  · intro b hb
    rcases Multiset.mem_add.mp hb with hb | hb
    · exact hP.2 b hb
    · exact hQ.2 b hb
  · simp [hcQ]

/-- Elementary minimization given Lemma 1 and a floor/delete certificate. -/
theorem upper_from_rounding_certificate
    (volume_bound : ∀ (J : Multiset ℝ), IsInstance J → (OPT J : ℝ) ≤ 2 * SIZE J + 1)
    (I : Multiset ℝ) (hI : IsInstance I) (x : Multiset ℝ →₀ ℝ)
    (hcert : RoundingCertificate I x) :
    (OPT I : ℝ) ≤ lpCost x + ((x.support.card : ℝ) + 1) / 2 := by
  obtain ⟨P, hP, hcard, hsize, hcover⟩ := hcert
  have hRI : residual I x ≤ I := Multiset.sub_le_self _ _
  have hR : IsInstance (residual I x) := fun t ht =>
    hI t (Multiset.mem_of_le hRI ht)
  have hvol := volume_bound (residual I x) hR
  have hglue : (OPT I : ℝ) ≤ (P.card : ℝ) + (OPT (residual I x) : ℝ) := by
    exact_mod_cast opt_le_card_add_opt I (residual I x) hI hRI P hP
  have hcard' : (P.card : ℝ) ≤ (principalCount x : ℝ) := by exact_mod_cast hcard
  linarith

/-- Sparse approximate optima and floor/delete certificates imply the exact upper
bound, without requiring attainment of the real infimum defining LIN. -/
theorem upper_from_sparse_approx_and_rounding
    (volume_bound : ∀ (J : Multiset ℝ), IsInstance J → (OPT J : ℝ) ≤ 2 * SIZE J + 1)
    (sparse_approx : ∀ (J : Multiset ℝ), IsInstance J → ∀ ε : ℝ, 0 < ε →
      ∃ x : Multiset ℝ →₀ ℝ,
        IsLPFeasible J x ∧ lpCost x < LIN J + ε ∧ x.support.card ≤ numSizes J)
    (rounding : ∀ (J : Multiset ℝ), IsInstance J → ∀ x : Multiset ℝ →₀ ℝ,
      IsLPFeasible J x → RoundingCertificate J x)
    (I : Multiset ℝ) (hI : IsInstance I) :
    (OPT I : ℝ) ≤ LIN I + ((numSizes I : ℝ) + 1) / 2 := by
  by_contra hn
  push Not at hn
  let ε : ℝ := ((OPT I : ℝ) - (LIN I + ((numSizes I : ℝ) + 1) / 2)) / 2
  have he : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨x, hx, hcost, hsupp⟩ := sparse_approx I hI ε he
  have hr := upper_from_rounding_certificate volume_bound I hI x (rounding I hI x hx)
  have hsupp' : (x.support.card : ℝ) ≤ (numSizes I : ℝ) := by exact_mod_cast hsupp
  dsimp [ε] at hcost
  linarith

end KKRoundingUpper

theorem solution (I : Multiset ℝ) (hI : IsInstance I) :
    SIZE I ≤ LIN I ∧ LIN I ≤ (OPT I : ℝ) ∧
      (OPT I : ℝ) ≤ LIN I + ((numSizes I : ℝ) + 1) / 2 := by
  refine ⟨size_le_lin I hI, lin_le_opt I hI, ?_⟩
  apply KKRoundingUpper.upper_from_sparse_approx_and_rounding
    opt_le_two_size_add_one exists_sparse_near_optimal_lp
    (fun J hJ x hx => ?_) I hI
  simpa only [KKRoundingUpper.RoundingCertificate, KKRoundingUpper.residual] using
    lp_floor_rounding_certificate J hJ x hx
