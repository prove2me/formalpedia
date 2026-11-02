-- Prove2me | solution 1 for JumpAmbiguity.Decomp.separation_A8
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T21:38:14.678925+00:00
-- url     : https://prove2.me/submissions/39e2b931-3976-4c1b-ae06-f1b515b1a7f7

import Mathlib
import Definitions.Def_JumpAmbiguity_Decomp_Model
import Theorems.Thm_JumpAmbiguity_Decomp_proposition_1
import Theorems.Thm_JumpAmbiguity_Decomp_decomposition_15
import Theorems.Thm_JumpAmbiguity_Decomp_jump_exposure

namespace JumpAmbiguity.Decomp
open Matrix

lemma sig_dot {m n : ℕ} (M : Market m n) (hS : M.Standing) (π c : Fin m → ℝ) :
    (M.Sig.transpose *ᵥ π) ⬝ᵥ (M.Sig⁻¹ *ᵥ c) = π ⬝ᵥ c := by
  have hSig : IsUnit M.Sig.det := hS.2.1
  rw [dotProduct_mulVec, mulVec_transpose, vecMul_vecMul,
    Matrix.mul_nonsing_inv _ hSig, vecMul_one]

lemma innerInf_eq {m n : ℕ} (M : Market m n) (hS : M.Standing)
    (hI : M.JumpIntegrable) (k : Fin n) (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    M.innerInf k a = M.innerObj k a (M.thetaStar k a) (M.varphiStar k a) :=
  (proposition_1 M hS hI k a ha).2.1.csInf_eq

theorem separation_A8_aux {m n : ℕ} (M : Market m n) (hS : M.Standing)
    (hI : M.JumpIntegrable) (π : Fin m → ℝ) (hπ : π ∈ M.Admissible) :
    M.generator π = M.r + M.diffusionObj (M.piperp π) + M.reducedObj (M.pibar π) := by
  have hd := (decomposition_15 M hS).2
  obtain ⟨hx, hy, -, -⟩ := hd (M.pihat π)
  obtain ⟨hmb, hmp, -, -⟩ := hd M.muhat
  have hpi : M.pihat π = M.pibar π + M.piperp π := by
    simp only [Market.piperp, Market.pibar]; abel
  have hmu : M.muhat = M.mubar + M.muperp := by
    simp only [Market.muperp, Market.mubar]; abel
  have hret : π ⬝ᵥ (M.mu - M.r • (1 : Fin m → ℝ)) = M.pihat π ⬝ᵥ M.muhat :=
    (sig_dot M hS π _).symm
  have hsum : ∑ k : Fin n, M.innerInf k (π ⬝ᵥ M.col k) =
      ∑ k : Fin n, M.innerObj k (M.pibar π ⬝ᵥ M.Jhatcol k)
        (M.thetaStar k (M.pibar π ⬝ᵥ M.Jhatcol k))
        (M.varphiStar k (M.pibar π ⬝ᵥ M.Jhatcol k)) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [jump_exposure M hS π k]
    apply innerInf_eq M hS hI
    rw [← jump_exposure M hS π k]; exact hπ k
  have c1 : M.piperp π ⬝ᵥ M.pibar π = 0 := hy _ hx
  have c2 : M.pibar π ⬝ᵥ M.piperp π = 0 := by rw [dotProduct_comm]; exact c1
  have c3 : M.muperp ⬝ᵥ M.pibar π = 0 := hmp _ hx
  have c3' : M.pibar π ⬝ᵥ M.muperp = 0 := by rw [dotProduct_comm]; exact c3
  have c4 : M.piperp π ⬝ᵥ M.mubar = 0 := hy _ hmb
  have c5 : M.mubar ⬝ᵥ M.pibar π = M.pibar π ⬝ᵥ M.mubar := dotProduct_comm _ _
  unfold Market.generator Market.diffusionObj Market.reducedObj
  rw [hsum, hret]
  change -(M.γ / 2) * (M.pihat π ⬝ᵥ M.pihat π) + _ + _ + _ = _
  rw [hpi, hmu]
  simp only [add_dotProduct, dotProduct_add]
  rw [c1, c2, c3', c4, c5]
  ring

end JumpAmbiguity.Decomp

open JumpAmbiguity.Decomp

theorem solution {m n : ℕ} (M : Market m n) (hS : M.Standing)
    (hI : M.JumpIntegrable) (π : Fin m → ℝ) (hπ : π ∈ M.Admissible) :
    M.generator π = M.r + M.diffusionObj (M.piperp π) + M.reducedObj (M.pibar π) :=
  JumpAmbiguity.Decomp.separation_A8_aux M hS hI π hπ
