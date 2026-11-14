-- Prove2me | solution 1 for Matrix.GeneralLinearGroup.larsen_alternative_of_fourth_moment
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-14T04:26:59.128123+00:00
-- url     : https://prove2.me/submissions/986b15b1-9287-4b8c-a654-0270aa3b8cf1

import Mathlib
import Definitions.Def_RPLib_S4_LarsenOSp

set_option autoImplicit false

theorem solution
    {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (G : Subgroup (Matrix.GeneralLinearGroup n K))
    (hGc : ∃ S : Set (MvPolynomial ((n × n) ⊕ (n × n)) K), ∀ g : Matrix.GeneralLinearGroup n K,
      g ∈ G ↔ ∀ p ∈ S, MvPolynomial.eval (Sum.elim (fun ij : n × n => (g : Matrix n n K) ij.1 ij.2)
        (fun ij : n × n => ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K) ij.1 ij.2)) p = 0)
    (hG : ∀ W : Submodule K (n → K), (∀ g ∈ G, ∀ v ∈ W, Matrix.mulVec (g : Matrix n n K) v ∈ W) → W = ⊥ ∨ W = ⊤)
    (M : ℕ)
    (hM : Module.finrank K (Submodule.span K {φ : Matrix n n K →ₗ[K] Matrix n n K | ∀ g ∈ G,
      ∀ x : Matrix n n K, φ ((g : Matrix n n K) * x * ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K)) =
        (g : Matrix n n K) * φ x * ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K)}) = M) :
    (2 ≤ Fintype.card n →
        ((fun g : Matrix.GeneralLinearGroup n K => (g : Matrix n n K).det) ''
          (G : Set (Matrix.GeneralLinearGroup n K))).Finite → M = 2 →
        Finite G ∨ ((Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup n K →* Kˣ).ker ≤ G ∧
          ((Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup n K →* Kˣ).ker.subgroupOf G).FiniteIndex)) ∧
      (3 ≤ Fintype.card n → ∀ B : Matrix n n K, Matrix.transpose B = B → B.Nondegenerate →
        (∀ g ∈ G, Matrix.transpose (g : Matrix n n K) * B * g = B) → M = 3 →
        Finite G ∨
          (∀ g : Matrix.GeneralLinearGroup n K,
            g ∈ G ↔ (Matrix.transpose (g : Matrix n n K) * B * g = B ∧ (g : Matrix n n K).det = 1)) ∨
          (∀ g : Matrix.GeneralLinearGroup n K, g ∈ G ↔ Matrix.transpose (g : Matrix n n K) * B * g = B)) ∧
      (3 ≤ Fintype.card n → ∀ B : Matrix n n K, Matrix.transpose B = -B → B.Nondegenerate →
        (∀ g ∈ G, Matrix.transpose (g : Matrix n n K) * B * g = B) → M = 3 →
        Finite G ∨ (∀ g : Matrix.GeneralLinearGroup n K, g ∈ G ↔ Matrix.transpose (g : Matrix n n K) * B * g = B)) := by
  obtain ⟨S, hS⟩ := hGc
  have hset : (G : Set (Matrix.GeneralLinearGroup n K)) = RamanujanPetersson.AlgGrpA.zeroS S :=
    Set.ext fun g => hS g
  have hGc' : @IsClosed (Matrix.GeneralLinearGroup n K) RamanujanPetersson.AlgGrpA.zarTop
      (G : Set (Matrix.GeneralLinearGroup n K)) := by
    rw [hset]
    exact RamanujanPetersson.AlgGrpA.isClosed_zeroS S
  have hspan : Submodule.span K {φ : Matrix n n K →ₗ[K] Matrix n n K | ∀ g ∈ G,
      ∀ x : Matrix n n K, φ ((g : Matrix n n K) * x * ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K)) =
        (g : Matrix n n K) * φ x * ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K)} =
      RamanujanPetersson.Larsen.adComm G :=
    Submodule.span_eq (RamanujanPetersson.Larsen.adComm G)
  have hM4 : RamanujanPetersson.Larsen.M4 G = M := by
    unfold RamanujanPetersson.Larsen.M4
    rw [← hspan]
    exact hM
  have hker : (Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup n K →* Kˣ).ker =
      RamanujanPetersson.AlgGrpB.detOne := by
    ext g
    rw [MonoidHom.mem_ker, RamanujanPetersson.AlgGrpB.mem_detOne, Units.ext_iff]
    simp
  have hiso : ∀ (B : Matrix n n K) (g : Matrix.GeneralLinearGroup n K),
      g ∈ RamanujanPetersson.AlgGrpB.isoSub B ↔ Matrix.transpose (g : Matrix n n K) * B * g = B :=
    fun _ _ => RamanujanPetersson.AlgGrpB.mem_isoSub
  refine ⟨fun hn hdet hM2 => ?_, fun hn B hB hnd hGB hM3 => ?_, fun hn B hB hnd hGB hM3 => ?_⟩
  · rw [hker]
    exact RamanujanPetersson.Larsen.larsen_sl hn hGc' hG hdet (hM4.trans hM2)
  · rcases RamanujanPetersson.Larsen.larsen_orth hB hnd hn hGc' (fun g hg => (hiso B g).2 (hGB g hg)) hG
        (hM4.trans hM3) with h | h | h
    · exact Or.inl h
    · refine Or.inr (Or.inl fun g => ?_)
      rw [h, Subgroup.mem_inf, hiso, RamanujanPetersson.AlgGrpB.mem_detOne]
    · refine Or.inr (Or.inr fun g => ?_)
      rw [h, hiso]
  · rcases RamanujanPetersson.Larsen.larsen_symp hB hnd hn hGc' (fun g hg => (hiso B g).2 (hGB g hg)) hG
        (hM4.trans hM3) with h | h
    · exact Or.inl h
    · refine Or.inr fun g => ?_
      rw [h, hiso]
