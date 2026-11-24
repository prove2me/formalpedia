-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CongruenceBasis.inv_mem_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:24:27.041963+00:00
-- url     : https://prove2.me/submissions/6bec2b1b-dd75-43c6-ad82-1756b25547cc

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsCongruenceSubset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Filter Topology Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CongruenceBasis
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.CompanionTheory.CongruenceBasis
theorem _root_.solution {N : ℕ} {t : ValueGroupWithZero k} (ht : t < 1) (g : GL (Fin N) k)
    (hg : ∀ i j, valuation k ((g : Matrix (Fin N) (Fin N) k) i j -
      (1 : Matrix (Fin N) (Fin N) k) i j) ≤ t) (i j : Fin N) :
    valuation k (((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j -
      (1 : Matrix (Fin N) (Fin N) k) i j) ≤ t := by
  set A : Matrix (Fin N) (Fin N) k := (g : Matrix (Fin N) (Fin N) k) - 1 with hA
  set B : Matrix (Fin N) (Fin N) k := ((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) - 1 with hB
  have hAle : ∀ i j, valuation k (A i j) ≤ t := fun i j => by simpa [hA] using hg i j
  have hrel : B = -A - A * B := by
    have hgh : (g : Matrix (Fin N) (Fin N) k) * ((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hg' : (g : Matrix (Fin N) (Fin N) k) = A + 1 := by simp [hA]
    have hh' : ((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) = B + 1 := by simp [hB]
    rw [hg', hh'] at hgh
    have : (A + 1) * (B + 1) = A * B + A + B + 1 := by noncomm_ring
    rw [this] at hgh
    have h3 : A * B + A + B = 0 := by simpa using hgh
    rw [eq_sub_iff_add_eq, eq_neg_iff_add_eq_zero, ← h3]
    abel
  show valuation k (B i j) ≤ t
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨⟨i₀, j₀⟩, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin N × Fin N))
    (fun p => valuation k (B p.1 p.2)) ⟨(i, j), Finset.mem_univ _⟩
  set M := valuation k (B i₀ j₀) with hM
  have hMt : t < M := lt_of_lt_of_le hcon (hmax (i, j) (Finset.mem_univ _))
  have hM0 : 0 < M := lt_of_le_of_lt zero_le' hMt
  have hprod : valuation k ((A * B) i₀ j₀) ≤ t * M := by
    rw [Matrix.mul_apply]
    refine Valuation.map_sum_le _ fun l _ => ?_
    rw [map_mul]
    exact mul_le_mul' (hAle _ _) (hmax (l, j₀) (Finset.mem_univ _))
  have htM : t * M < M := by
    simpa using mul_lt_mul_of_pos_right ht hM0
  have hent : B i₀ j₀ = -A i₀ j₀ - (A * B) i₀ j₀ := by
    conv_lhs => rw [hrel]
    simp
  have : M < M := by
    calc M = valuation k (-A i₀ j₀ - (A * B) i₀ j₀) := by rw [hM, ← hent]
      _ ≤ max (valuation k (-A i₀ j₀)) (valuation k ((A * B) i₀ j₀)) := Valuation.map_sub _ _ _
      _ < M := by
        refine max_lt ?_ (lt_of_le_of_lt hprod htM)
        rw [Valuation.map_neg]
        exact lt_of_le_of_lt (hAle _ _) hMt
  exact lt_irrefl _ this
end GlobalTheory.CompanionTheory.CongruenceBasis
