-- Prove2me | solution 1 for GlobalTheory.AffGlue.Cech.exists_glue_finset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:43:15.121751+00:00
-- url     : https://prove2.me/submissions/2e390f5c-0977-4053-8f11-dbf9adfff803

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SecEquivResM
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AffineCoverSectionsGlue
import Theorems.Thm_GlobalTheory_AffGlue_Cech_span_small_eq_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AffGlue
open GlobalTheory GlobalTheory.AffGlue GlobalTheory.AffGlue.Cech
variable {T : Scheme.{0}}
namespace GlobalTheory.AffGlue.Cech
theorem _root_.solution (D : Data T) {V : T.Opens} (hV : IsAffineOpen V) {ι : Type}
    (W : ι → T.Opens) (hW : ∀ i, IsAffineOpen (W i)) (hWV : ∀ i, W i ≤ V) (hc : V ≤ ⨆ i, W i)
    (m : ∀ i, D.M (W i) (hW i))
    (hm : ∀ (i j : ι) (O : T.Opens) (hO : IsAffineOpen O) (hi : O ≤ W i) (hj : O ≤ W j),
      D.ρ (hW i) hO hi (m i) = D.ρ (hW j) hO hj (m j)) (s : Finset ι) :
    ∃ x : D.M V hV, ∀ k ∈ s, D.ρ hV (hW k) (hWV k) x = m k := by
  let I : Ideal Γ(T, V) :=
    { carrier := {a | ∃ x : D.M V hV, ∀ k ∈ s, D.ρ hV (hW k) (hWV k) x = resG T (hWV k) a • m k}
      add_mem' := by
        rintro a b ⟨x, hx⟩ ⟨y, hy⟩
        exact ⟨x + y, fun k hk => by rw [map_add, map_add, add_smul, hx k hk, hy k hk]⟩
      zero_mem' := ⟨0, fun k _ => by rw [map_zero, map_zero, zero_smul]⟩
      smul_mem' := by
        rintro c a ⟨x, hx⟩
        exact ⟨c • x, fun k hk => by
          rw [D.ρ_smul, hx k hk, smul_eq_mul, map_mul, mul_smul]⟩ }
  have h1 : (1 : Γ(T, V)) ∈ I := by
    refine Submodule.mem_of_span_eq_top_of_smul_pow_mem I _ (span_small_eq_top hV W hc) 1 ?_
    rintro ⟨f, i, hf⟩
    obtain ⟨N, x₀, hx₀⟩ := D.loc_surj hV f (hV.basicOpen f)
      (D.ρ (hW i) (hV.basicOpen f) hf (m i))
    have key : ∀ k, ∃ e : ℕ, resG T (hWV k) f ^ e •
        (D.ρ hV (hW k) (hWV k) x₀ - resG T (hWV k) f ^ N • m k) = 0 := by
      intro k
      refine D.loc_inj (hW k) (resG T (hWV k) f) ((hW k).basicOpen _) _ ?_
      have hle : T.basicOpen (resG T (hWV k) f) ≤ T.basicOpen f := by
        have := T.basicOpen_res f (homOfLE (hWV k)).op
        exact (le_of_eq this).trans inf_le_right
      have h2 := congrArg (D.ρ (hV.basicOpen f) ((hW k).basicOpen (resG T (hWV k) f)) hle) hx₀
      rw [D.ρ_ρ, D.ρ_smul, D.ρ_ρ, map_pow, resG_resG' _ _ (hle.trans (T.basicOpen_le f))] at h2
      rw [map_sub, D.ρ_ρ, D.ρ_smul, map_pow, resG_resG' _ _ (hle.trans (T.basicOpen_le f)),
        ← h2, hm i k _ _ _ (T.basicOpen_le _), sub_self]
    choose e he using key
    refine ⟨s.sup e + N, f ^ s.sup e • x₀, fun k hk => ?_⟩
    have hk' : e k ≤ s.sup e := Finset.le_sup hk
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le' hk'
    have h3 : resG T (hWV k) f ^ s.sup e •
        (D.ρ hV (hW k) (hWV k) x₀ - resG T (hWV k) f ^ N • m k) = 0 := by
      rw [hd, pow_add, mul_smul, he, smul_zero]
    rw [smul_sub, sub_eq_zero] at h3
    rw [D.ρ_smul, map_pow, h3, smul_eq_mul, mul_one, map_pow, pow_add, mul_smul]
  obtain ⟨x, hx⟩ := h1
  exact ⟨x, fun k hk => by rw [hx k hk, map_one, one_smul]⟩
end GlobalTheory.AffGlue.Cech
