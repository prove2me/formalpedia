-- Prove2me | solution 1 for ModularSchur.le_schurModResidue
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-19T23:02:33.706213+00:00
-- url     : https://prove2.me/submissions/1b9bbdd4-8f6d-413c-bd6b-1f498768c056

-- Generated from lean/ModularSchur/Partition.lean
--   imports : 1 platform node(s), 2 definition bundle(s)
--   inlined : 2 file-scoped / sub-threshold helper(s)
--   rename  : le_schurModResidue -> solution, hoisted out of the namespace
import Definitions.Def_ModularSchurBasic
import Definitions.Def_ModularSchurPartition
import Theorems.Thm_ModularSchur_singleton_sumFree_iff
import Mathlib

open Finset Nat
variable {m ℓ : ℕ}

namespace ModularSchur

theorem singleton_safe_in_stable_range (hm : 2 ≤ m) (hℓ : 2 ≤ ℓ)
    (r : ℕ) (hr1 : 1 ≤ r) (hr2 : r < m / Nat.gcd m (ℓ - 1)) :
    ((ℓ : ZMod m) - 1) * (r : ZMod m) ≠ 0 := by
  contrapose! hr2;
  refine' Nat.div_le_of_le_mul _;
  -- Since $m$ divides $(ℓ - 1) * r$, we have $m \mid (ℓ - 1) * r$.
  have h_div : m ∣ (ℓ - 1) * r := by
    cases ℓ <;> simp_all +decide [ ← ZMod.natCast_eq_zero_iff ];
  rw [ ← Nat.gcd_mul_right ];
  exact Nat.le_of_dvd ( by positivity ) ( Nat.dvd_gcd ( dvd_mul_right _ _ ) h_div )

theorem singleton_sumFree_in_stable_range (hm : 2 ≤ m) (hℓ : 2 ≤ ℓ)
    (r : ℕ) (hr1 : 1 ≤ r) (hr2 : r < m / Nat.gcd m (ℓ - 1)) :
    IsEllSumFree m ℓ {(r : ZMod m)} := by
  exact ( singleton_sumFree_iff ℓ ( by linarith ) _ ) |>.mpr ( singleton_safe_in_stable_range hm hℓ r hr1 hr2 )

end ModularSchur

open ModularSchur in
theorem solution (m k ℓ : ℕ) (hm : 2 ≤ m) (hℓ : 2 ≤ ℓ)
    (hk : m / Nat.gcd m (ℓ - 1) - 1 ≤ k) :
    m / Nat.gcd m (ℓ - 1) - 1 ≤ schurModResidue m k ℓ := by
  -- Let $n = m / \gcd(m, \ell - 1)$.
  set n := m / Nat.gcd m (ℓ - 1);
  apply_rules [ Nat.le_findGreatest ];
  · exact Nat.sub_le_sub_right ( Nat.div_le_self _ _ ) _;
  · -- Define the partition P as follows:
    -- For each i in Fin k, if i.val < n - 1, then P i is the singleton set containing (i.val + 1) in ZMod m.
    -- Otherwise, P i is the empty set.
    use fun i => if i.val < n - 1 then {(↑(i.val + 1) : ZMod m)} else ∅;
    constructor <;> norm_num;
    · intro x hx; unfold stableResidues at hx; simp_all +decide [ Fin.exists_iff ] ;
      obtain ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩ := hx; use a - 1; rcases a with ( _ | a ) <;> simp_all +decide ; omega;
    · intro i j hij; split_ifs <;> simp_all +decide [ Fin.ext_iff, Set.disjoint_left ] ;
      rw [ ZMod.natCast_eq_natCast_iff ];
      rw [ Nat.ModEq, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt ] <;> contrapose! hij <;> linarith [ Nat.div_le_self m ( Nat.gcd m ( ℓ - 1 ) ), Nat.sub_add_cancel ( show 1 ≤ m / Nat.gcd m ( ℓ - 1 ) from Nat.div_pos ( Nat.le_of_dvd ( by linarith ) ( Nat.gcd_dvd_left _ _ ) ) ( Nat.gcd_pos_of_pos_left _ ( by linarith ) ) ) ];
    · intro i; split_ifs <;> simp +decide [ *, stableResidues ] ;
      exact ⟨ i + 1, ⟨ Nat.succ_pos _, by linarith ⟩, by norm_cast ⟩;
    · intro i; split_ifs <;> simp_all +decide [ IsEllSumFree ] ;
      intro f hf; have := singleton_sumFree_in_stable_range hm hℓ ( i + 1 ) ( by linarith ) ( by omega ) ; simp_all +decide [ IsEllSumFree ] ;
