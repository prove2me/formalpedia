-- Prove2me | solution 1 for MvFormalGroup.exists_forall_coeff_nthSeries_pow_mem_span_of_isNilpotent_hasseWitt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/5a400ad8-7610-5e23-b3c7-9ee2dd959709

import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import Theorems.Thm_MvFormalGroup_coeff_nthSeries_pow_eq_zero_of_hasseWitt_pow_eq_zero_zmodp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_exists_forall_coeff_nthSeries_pow_mem_span_of_isNilpotent_hasseWitt
p2m_attr_erase "instance" "MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing"
p2m_attr_erase "simp" "MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg'"

set_option autoImplicit false

open MvPowerSeries

universe u v

namespace MvFormalGroup
p2m_export "MvFormalGroup" "IsComm map nthSeries nthSeries_zero nthSeries_succ IsComm.comm toPowerSeries constantCoeff_eq_zero coeff_nthSeries_pow_eq_zero_of_hasseWitt_pow_eq_zero_zmodp"
namespace GForm
p2m_open "MvFormalGroup~constantCoeff_nthSeries"

variable {R : Type u} [CommRing R] {S : Type v} [CommRing S] {d : ℕ}

private theorem constantCoeff_nthSeries (F : MvFormalGroup d R) (n : ℕ) (i : Fin d) :
    (F.nthSeries n i).constantCoeff = 0 := by
  induction n generalizing i with
  | zero => simp [nthSeries_zero]
  | succ n ih =>
    rw [nthSeries_succ]
    have hz : ∀ s : Fin d ⊕ Fin d,
        (Sum.elim (F.nthSeries n) (fun j => (X j : MvPowerSeries (Fin d) R)) s).constantCoeff = 0 := by
      rintro (j | j)
      · exact ih j
      · exact constantCoeff_X _
    exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hz) hz (F.constantCoeff_eq_zero i)

private theorem nthSeries_map (f : R →+* S) (F : MvFormalGroup d R) (n : ℕ) :
    (F.map f).nthSeries n = fun i => MvPowerSeries.map f (F.nthSeries n i) := by
  induction n with
  | zero => funext i; simp [nthSeries_zero]
  | succ n ih =>
    funext i
    have hz : ∀ s : Fin d ⊕ Fin d,
        (Sum.elim (F.nthSeries n) (fun j => (X j : MvPowerSeries (Fin d) R)) s).constantCoeff = 0 := by
      rintro (j | j)
      · exact constantCoeff_nthSeries F n j
      · exact constantCoeff_X _
    have ha := hasSubst_of_constantCoeff_zero hz
    rw [nthSeries_succ, nthSeries_succ, ih]
    change subst _ (MvPowerSeries.map f (F.toPowerSeries i)) = _
    rw [map_subst ha]
    congr 1
    funext s
    rcases s with j | j
    · rfl
    · simp [map_X]

private theorem isComm_map (f : R →+* S) (F : MvFormalGroup d R) [F.IsComm] : (F.map f).IsComm := by
  refine ⟨fun i => ?_⟩
  have hz : ∀ s : Fin d ⊕ Fin d, (Sum.elim (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) R))
      (fun j => X (Sum.inl j)) s).constantCoeff = 0 := by
    rintro (j | j) <;> exact constantCoeff_X _
  have ha := hasSubst_of_constantCoeff_zero hz
  have key := congrArg (MvPowerSeries.map f) (IsComm.comm (F := F) i)
  rw [map_subst ha] at key
  have hmap : (fun s => MvPowerSeries.map f (Sum.elim
      (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) R)) (fun j => X (Sum.inl j)) s)) =
      Sum.elim (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) S)) (fun j => X (Sum.inl j)) := by
    funext s
    rcases s with j | j <;> simp [map_X]
  rw [hmap] at key
  exact key

end MvFormalGroup.GForm

open MvFormalGroup.GForm in
theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime]
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    {d : ℕ} (F : MvFormalGroup d 𝓞) [F.IsComm]
    (hHW : IsNilpotent (Matrix.of fun i j : Fin d =>
      algebraMap 𝓞 (ZMod p) ((F.nthSeries p i).coeff (Finsupp.single j p)))) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ (i : Fin d) (n : Fin d →₀ ℕ), n.degree < p ^ (A + 1) →
      (F.nthSeries (p ^ A) i).coeff n ∈ Ideal.span {(p : 𝓞)} := by
  classical
  obtain ⟨ν, hν⟩ := hHW
  refine ⟨max ν 1, le_max_right _ _, fun i n hn => ?_⟩

  let f : 𝓞 →+* ZMod p := algebraMap 𝓞 (ZMod p)
  let Fb : MvFormalGroup d (ZMod p) := F.map f
  haveI : Fb.IsComm := MvFormalGroup.GForm.isComm_map f F
  have hBb : (Matrix.of fun i j : Fin d => (Fb.nthSeries p i).coeff (Finsupp.single j p)) =
      Matrix.of fun i j : Fin d => algebraMap 𝓞 (ZMod p) ((F.nthSeries p i).coeff (Finsupp.single j p)) := by
    ext i j
    simp only [Matrix.of_apply, Fb, MvFormalGroup.GForm.nthSeries_map, coeff_map]
    rfl
  have hA : (Matrix.of fun i j : Fin d => (Fb.nthSeries p i).coeff (Finsupp.single j p)) ^ (max ν 1) = 0 := by
    rw [hBb]
    exact pow_eq_zero_of_le (le_max_left _ _) hν
  by_cases hn0 : n = 0
  · subst hn0
    have : (F.nthSeries (p ^ max ν 1) i).coeff 0 = 0 := by
      rw [MvPowerSeries.coeff_zero_eq_constantCoeff]
      exact MvFormalGroup.GForm.constantCoeff_nthSeries F _ i
    rw [this]
    exact zero_mem _
  · obtain ⟨j, hj⟩ : ∃ j, n j ≠ 0 := by
      simpa using Finsupp.ne_iff.1 hn0
    have hjlt : n j < p ^ (max ν 1 + 1) := lt_of_le_of_lt (Finsupp.le_degree j n) hn
    have hndvd : ¬ p ^ (max ν 1 + 1) ∣ n j := fun h => hj (Nat.eq_zero_of_dvd_of_lt h hjlt)
    have key := MvFormalGroup.coeff_nthSeries_pow_eq_zero_of_hasseWitt_pow_eq_zero_zmodp p Fb (max ν 1) hA
      i n ⟨j, hndvd⟩
    have : algebraMap 𝓞 (ZMod p) ((F.nthSeries (p ^ max ν 1) i).coeff n) = 0 := by
      have h2 := key
      simp only [Fb, MvFormalGroup.GForm.nthSeries_map, coeff_map] at h2
      exact h2
    rw [← hker]
    exact (RingHom.mem_ker).2 this

end S_MvFormalGroup_exists_forall_coeff_nthSeries_pow_mem_span_of_isNilpotent_hasseWitt
end P2MW
export P2MW.S_MvFormalGroup_exists_forall_coeff_nthSeries_pow_mem_span_of_isNilpotent_hasseWitt (solution)
