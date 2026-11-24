-- Prove2me | solution 1 for GlobalTheory.FullLevel.exists_sympLevel_of_tate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:08:55.171796+00:00
-- url     : https://prove2.me/submissions/2129a3f9-c7d3-4dca-aac6-0c2fdf6b3d2b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSympLevel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFullSymplecticLevelStructureOfTateIso
import Theorems.Thm_GlobalTheory_FullLevel_exists_twist
import Theorems.Thm_GlobalTheory_FullLevel_smul_mem_M
import Theorems.Thm_P2M_GlobalTheory_FullLevel_A_dvd_M__c65dcadf2e66
import Theorems.Thm_P2M_GlobalTheory_FullLevel_M__pos_df9b3d1f4b28
import Theorems.Thm_P2M_GlobalTheory_FullLevel_M_dvd_M__ccc9399a2d7f


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.FullLevel
open ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
namespace GlobalTheory.FullLevel
theorem _root_.solution : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} (l : Level H) {k : Type} [Field k]
    {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop} (I : TateIso D k Q act e)
    {z : kˣ}, IsPrimitiveRoot z l.M' → z ^ (l.M' / l.A) = I.ζ l.A →
    ∃ ev : D.La → Q, IsSympLevel D act e l.M' z ev ∧ Induces l (I.ev l.A) (I.ev l.M) ev := by
  intro E _ _ _ H D l k _ Q _ act e I z hz hzA
  have hM' := M'_pos l
  haveI : NeZero l.M' := ⟨hM'.ne'⟩
  have hζ := I.ζ_prim l.M' hM'
  obtain ⟨L, -, hcop, hL⟩ := (hζ.isPrimitiveRoot_iff').1 hz
  obtain ⟨d, hd⟩ := A_dvd_M' l
  have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hd; omega)
  have hdiv : l.M' / l.A = d := by rw [hd, Nat.mul_div_cancel_left _ l.A_pos]
  have hζA : I.ζ l.M' ^ d = I.ζ l.A := by
    have := I.ζ_pow l.A d l.A_pos hd0; rwa [← hd] at this
  have hAL : (l.A : ℤ) ∣ (L : ℤ) - 1 := by
    have e1 : I.ζ l.M' ^ (L * d) = I.ζ l.M' ^ d := by
      rw [pow_mul, hL, ← hdiv, hzA, hdiv, hζA]
    have h2 : I.ζ l.M' ^ (((L : ℤ) - 1) * d) = 1 := by
      rw [sub_mul, one_mul, zpow_sub, show ((L : ℤ) * d) = ((L * d : ℕ) : ℤ) by push_cast; ring,
        zpow_natCast, zpow_natCast, e1, mul_inv_cancel]
    have h3 := (hζ.zpow_eq_one_iff_dvd _).1 h2
    rw [hd] at h3; push_cast at h3
    exact (mul_dvd_mul_iff_right (by exact_mod_cast hd0.ne')).1 h3
  obtain ⟨a', b', hab⟩ := Nat.isCoprime_iff_coprime.2 hcop
  obtain ⟨u, w, c, hc, hu, hw⟩ := exists_twist l L hAL
  set v : 𝓞 E := (a' : 𝓞 E) * H.bar u with hv
  have hvu : v * u = 1 + (l.M' : 𝓞 E) * ((a' : 𝓞 E) * w - b') := by
    have hab' : (a' : 𝓞 E) * (L : ℤ) + (b' : 𝓞 E) * ((l.M' : ℕ) : ℤ) = 1 := by exact_mod_cast hab
    push_cast at hab'
    rw [hv, mul_assoc, hw]
    push_cast
    linear_combination hab'
  have key : ∀ a : D.La, v • u • a = a + l.M' • (((a' : 𝓞 E) * w - b') • a) := by
    intro a; rw [← mul_smul, hvu, add_smul, one_smul, mul_smul, Nat.cast_smul_eq_nsmul]
  have key' : ∀ a : D.La, u • v • a = a + l.M' • (((a' : 𝓞 E) * w - b') • a) := by
    intro a; rw [smul_comm]; exact key a
  have hcong : ∀ a b : D.La, I.ev l.M' (a + l.M' • b) = I.ev l.M' a := by
    intro a b; rw [I.add, (I.ker _ hM' _).2 ⟨b, rfl⟩, mul_one]
  have hEF : ∀ a b : D.La, D.EF (u • a) (u • b) = L * D.EF a b + l.M' * D.EF a (w • b) := by
    intro a b
    rw [D.adj, ← mul_smul, hw, add_smul, mul_smul, Nat.cast_smul_eq_nsmul]
    simp only [Int.cast_natCast, Nat.cast_smul_eq_nsmul, map_add, map_zsmul, map_nsmul, smul_eq_mul, nsmul_eq_mul]
  refine ⟨fun a => I.ev l.M' (u • a), ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro a b; simp only [smul_add, I.add]
  · intro c a; try simp only
    rw [smul_comm, I.lin]
  · intro a; try simp only
    rw [I.ker _ hM']
    constructor
    · rintro ⟨b, hb⟩
      refine ⟨v • b - ((a' : 𝓞 E) * w - b') • a, ?_⟩
      have h := congrArg (v • ·) hb
      change v • u • a = v • (l.M' • b) at h
      rw [key, smul_comm v l.M' b] at h
      rw [smul_sub, ← h]; abel
    · rintro ⟨b, rfl⟩; exact ⟨u • b, smul_comm _ _ _⟩
  · intro x; rw [I.onto _ hM']
    constructor
    · rintro ⟨a0, rfl⟩; exact ⟨v • a0, by simp only [key', hcong]⟩
    · rintro ⟨a, rfl⟩; exact ⟨u • a, rfl⟩
  · intro a b
    have h := I.isom _ hM' (u • a) (u • b)
    convert h using 1
    rw [hEF, zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, hL, hζ.pow_eq_one, one_zpow, mul_one]
  · intro a
    have htow : I.ev l.M' (u • a) ^ d = I.ev l.A (u • a) := by
      have := I.tower l.A d l.A_pos hd0 (u • a); rwa [← hd] at this
    try simp only
    rw [hdiv, htow, hu, add_smul, one_smul, mul_smul, Nat.cast_smul_eq_nsmul, I.add,
      (I.ker _ l.A_pos _).2 ⟨_, rfl⟩, mul_one]
  · intro a ha
    obtain ⟨dM, hdM⟩ := M_dvd_M' l
    have hMp : 0 < l.M := by have := l.three_le; omega
    have hdM0 : 0 < dM := Nat.pos_of_ne_zero (by rintro rfl; simp at hdM; omega)
    have hdivM : l.M' / l.M = dM := by rw [hdM, Nat.mul_div_cancel_left _ hMp]
    have htow : I.ev l.M' (u • a) ^ dM = I.ev l.M (u • a) := by
      have := I.tower l.M dM hMp hdM0 (u • a); rwa [← hdM] at this
    obtain ⟨y, hy⟩ := smul_mem_M l hc ha
    try simp only
    rw [hdivM, htow, hu, add_smul, one_smul, mul_smul, hy, Nat.cast_smul_eq_nsmul, smul_comm, I.add,
      (I.ker _ hMp _).2 ⟨_, rfl⟩, mul_one]
end GlobalTheory.FullLevel
