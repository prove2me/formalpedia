-- Prove2me | solution 1 for GlobalTheory.FinWeil.exists_extension_of_dense
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:09:08.748532+00:00
-- url     : https://prove2.me/submissions/578ea7a2-3b88-45ed-84f7-7ca71ba589ae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsExtensionOfDense

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical GlobalTheory.FinWeil
open scoped BigOperators
open GlobalTheory GlobalTheory.FinWeil
namespace GlobalTheory.FinWeil
theorem _root_.solution {X₀ X M : Type} [AddCommGroup X₀] [AddCommGroup X]
    [AddCommGroup M] [Module ℂ M] (ι : X₀ →+ X) (A : AddSubgroup X) (β : X → X → ℂ)
    (W₀ : X₀ → M →ₗ[ℂ] M)
    (hl : ∀ x y z, β (x + y) z = β x z * β y z)
    (hr : ∀ x y z, β x (y + z) = β x y * β x z)
    (hA : ∀ a ∈ A, ∀ b ∈ A, β a b = 1)
    (hβ : ∀ x, ∃ m : ℕ, 0 < m ∧ ∀ a ∈ A, β x (m • a) = 1 ∧ β (m • a) x = 1)
    (hW : ∀ x y v, W₀ x (W₀ y v) = β (ι x) (ι y) • W₀ (x + y) v)
    (hd : ∀ (x : X) (m : ℕ), 0 < m → ∃ z, ∃ a ∈ A, ι z = x + m • a)
    (hs : ∀ v, ∃ m : ℕ, 0 < m ∧ ∀ z, (∃ a ∈ A, ι z = m • a) → W₀ z v = v) :
    ∃ W : X → M →ₗ[ℂ] M, (∀ z, W (ι z) = W₀ z) ∧
      (∀ x y v, W x (W y v) = β x y • W (x + y) v) ∧
      ∀ x v, ∃ m : ℕ, 0 < m ∧ ∀ a ∈ A, W (x + m • a) v = W x v := by
  choose b hb0 hb using hβ
  have hb' : ∀ x (n : ℕ), b x ∣ n → ∀ a ∈ A, β x (n • a) = 1 ∧ β (n • a) x = 1 := by
    rintro x n ⟨k, rfl⟩ a ha
    rw [mul_smul]
    exact hb x _ (A.nsmul_mem ha k)
  have hex : ∀ (x : X) (v : M), ∃ G : M, ∃ m : ℕ, 0 < m ∧
      ∀ n : ℕ, m ∣ n → ∀ z, ∀ a ∈ A, ι z = x + n • a → W₀ z v = G := by
    intro x v
    obtain ⟨m, hm0, hm⟩ := hs v
    obtain ⟨z₁, a₁, ha₁, hz₁⟩ := hd x (m * b x) (Nat.mul_pos hm0 (hb0 x))
    refine ⟨W₀ z₁ v, m * b x, Nat.mul_pos hm0 (hb0 x), ?_⟩
    rintro n ⟨k, rfl⟩ z a ha hz
    rw [mul_smul] at hz
    have ha' : k • a ∈ A := A.nsmul_mem ha k
    have hsub : a₁ - k • a ∈ A := A.sub_mem ha₁ ha'
    have hιd : ι (z₁ - z) = (m * b x) • (a₁ - k • a) := by
      rw [map_sub, hz₁, hz, smul_sub]; abel
    have h1 : W₀ (z₁ - z) v = v :=
      hm _ ⟨b x • (a₁ - k • a), A.nsmul_mem hsub _, by rw [hιd, mul_smul]⟩
    have h2 := hW z (z₁ - z) v
    rw [h1, hιd, hz, hl, (hb' x _ (Dvd.intro_left m rfl) _ hsub).1,
      hA _ (A.nsmul_mem ha' _) _ (A.nsmul_mem hsub _), add_sub_cancel] at h2
    simpa using h2
  choose val lev hlev0 hlev using hex
  refine ⟨fun x =>
    { toFun := val x
      map_add' := ?_
      map_smul' := ?_ }, ?_, ?_, ?_⟩
  · intro v w
    obtain ⟨z, a, ha, hz⟩ := hd x (lev x v * lev x w * lev x (v + w))
      (Nat.mul_pos (Nat.mul_pos (hlev0 _ _) (hlev0 _ _)) (hlev0 _ _))
    rw [← hlev x v _ ⟨lev x w * lev x (v + w), by ring⟩ z a ha hz,
      ← hlev x w _ ⟨lev x v * lev x (v + w), by ring⟩ z a ha hz,
      ← hlev x (v + w) _ ⟨lev x v * lev x w, by ring⟩ z a ha hz, map_add]
  · intro c v
    obtain ⟨z, a, ha, hz⟩ := hd x (lev x v * lev x (c • v))
      (Nat.mul_pos (hlev0 _ _) (hlev0 _ _))
    rw [← hlev x v _ ⟨lev x (c • v), by ring⟩ z a ha hz,
      ← hlev x (c • v) _ ⟨lev x v, by ring⟩ z a ha hz, map_smul, RingHom.id_apply]
  · intro z
    ext v
    exact (hlev (ι z) v _ dvd_rfl z 0 A.zero_mem (by simp)).symm
  · intro x y v
    change val x (val y v) = β x y • val (x + y) v
    obtain ⟨n, hn0, h1, h2, h3, h4, h5⟩ : ∃ n : ℕ, 0 < n ∧ lev x (val y v) ∣ n ∧ lev y v ∣ n ∧
        lev (x + y) v ∣ n ∧ b x ∣ n ∧ b y ∣ n :=
      ⟨lev x (val y v) * lev y v * lev (x + y) v * b x * b y,
        Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (hlev0 _ _) (hlev0 _ _)) (hlev0 _ _))
          (hb0 _)) (hb0 _),
        ⟨lev y v * lev (x + y) v * b x * b y, by ring⟩,
        ⟨lev x (val y v) * lev (x + y) v * b x * b y, by ring⟩,
        ⟨lev x (val y v) * lev y v * b x * b y, by ring⟩,
        ⟨lev x (val y v) * lev y v * lev (x + y) v * b y, by ring⟩,
        ⟨lev x (val y v) * lev y v * lev (x + y) v * b x, by ring⟩⟩
    obtain ⟨z, a, ha, hz⟩ := hd x n hn0
    obtain ⟨w, c, hc, hw⟩ := hd y n hn0
    have hzw : ι (z + w) = x + y + n • (a + c) := by
      rw [map_add, hz, hw, smul_add]; abel
    have hβzw : β (ι z) (ι w) = β x y := by
      rw [hz, hw, hl, hr, hr, (hb' x n h4 c hc).1, (hb' y n h5 a ha).2,
        hA _ (A.nsmul_mem ha n) _ (A.nsmul_mem hc n)]
      ring
    rw [← hlev x (val y v) n h1 z a ha hz, ← hlev (x + y) v n h3 (z + w) _ (A.add_mem ha hc) hzw,
      ← hlev y v n h2 w c hc hw, hW, hβzw]
  · intro x v
    refine ⟨lev x v, hlev0 _ _, fun a ha => ?_⟩
    change val (x + lev x v • a) v = val x v
    obtain ⟨z, c, hc, hz⟩ := hd (x + lev x v • a) (lev x v * lev (x + lev x v • a) v)
      (Nat.mul_pos (hlev0 _ _) (hlev0 _ _))
    rw [← hlev _ v _ (Dvd.intro_left _ rfl) z c hc hz]
    refine hlev x v _ dvd_rfl z (a + lev (x + lev x v • a) v • c)
      (A.add_mem ha (A.nsmul_mem hc _)) ?_
    rw [hz, smul_add, mul_smul, add_assoc]
end GlobalTheory.FinWeil
