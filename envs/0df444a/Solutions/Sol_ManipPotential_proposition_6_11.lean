-- Prove2me | solution 1 for ManipPotential.proposition_6_11
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:31:08.937297+00:00
-- url     : https://prove2.me/submissions/4f6602f5-764e-4923-9770-c465783dd26b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_ManipPotential_proposition_6_11_sperner_existence
import Theorems.Thm_ManipPotential_proposition_6_11_uniqueness_lipschitz
import Theorems.Thm_ManipPotential_proposition_6_11_rank
import Definitions.Def_ManipPotential_GAxioms
import Definitions.Def_ManipPotential_IsCommonJunction
import Definitions.Def_ManipPotential_ExtRanking
import Definitions.Def_ManipPotential_cycTotal
open ManipPotential
/-- Proposition 6.11, assembled from its existence, uniqueness/Lipschitz, and rank steps. -/
theorem solution {m : ℕ} [NeZero m] (hm : 3 ≤ m) (K : ℕ) (g : (Ranking m → ℚ) → Fin m)
    (hg : GAxioms K g) :
    ∃ (a b : ExtRanking m → ℝ) (a₀ b₀ : ℝ) (U : Set ((ExtRanking m → ℝ) × ℝ)) (L : NNReal)
      (G : (ExtRanking m → ℝ) × ℝ → (Ranking m → ℝ)),
      (∀ s, a s < b s) ∧ a₀ < b₀ ∧
      U = (Set.univ.pi fun s => Set.Ioo (a s) (b s)) ×ˢ Set.Ioo a₀ b₀ ∧
      LipschitzOnWith L G U ∧
      (∀ z ∈ U, (∀ s : ExtRanking m, G z s.1 = z.1 s) ∧ cycTotal (G z) = z.2) ∧
      (∀ z ∈ U, IsCommonJunction g (G z)) ∧
      (∀ z ∈ U, ∀ P : Ranking m → ℝ, IsCommonJunction g P →
        (∀ s : ExtRanking m, P s.1 = z.1 s) → cycTotal P = z.2 → P = G z) ∧
      (∀ z ∈ U, ∀ r, 1 < G z r) ∧
      (∀ z ∈ U, DifferentiableAt ℝ G z →
        Module.finrank ℝ (LinearMap.range (fderiv ℝ G z).toLinearMap) = m.factorial - m + 1) := by
  classical
  obtain ⟨T, hmT, hex⟩ := proposition_6_11_sperner_existence hm K g hg
  obtain ⟨L, hLip₀⟩ := proposition_6_11_uniqueness_lipschitz hm K g hg
  let a : ExtRanking m → ℝ := fun _ => 1
  let b : ExtRanking m → ℝ := fun _ => 1 + 1 / 32
  let U : Set ((ExtRanking m → ℝ) × ℝ) :=
    (Set.univ.pi fun s => Set.Ioo (a s) (b s)) ×ˢ Set.Ioo T (T + 1)
  have hbox {z : (ExtRanking m → ℝ) × ℝ} (hz : z ∈ U) :
      (∀ s, 1 < z.1 s ∧ z.1 s < 1 + 1 / 32) ∧ T < z.2 ∧ z.2 < T + 1 := by
    rcases hz with ⟨hy, hτ⟩
    refine ⟨?_, hτ.1, hτ.2⟩
    intro s
    exact hy s (Set.mem_univ s)
  have hpos_of {z : (ExtRanking m → ℝ) × ℝ} (hz : z ∈ U) {P : Ranking m → ℝ}
      (hP : IsCommonJunction g P) (hPe : ∀ s : ExtRanking m, P s.1 = z.1 s)
      (hPτ : cycTotal P = z.2) : ∀ r, 1 < P r := by
    obtain ⟨hb, hT, hT1⟩ := hbox hz
    exact (hex z.1 z.2 hb hT hT1).1 P hP hPe hPτ
  have hexz (z : (ExtRanking m → ℝ) × ℝ) :
      ∃ P : Ranking m → ℝ, z ∈ U →
        IsCommonJunction g P ∧ (∀ s : ExtRanking m, P s.1 = z.1 s) ∧
          cycTotal P = z.2 ∧ ∀ r, 1 < P r := by
    by_cases hz : z ∈ U
    · obtain ⟨hy, hT, hT1⟩ := hbox hz
      obtain ⟨hpositive, P, hP, hPy, hPτ, hpos⟩ := hex z.1 z.2 hy hT hT1
      exact ⟨P, fun _ => ⟨hP, hPy, hPτ, hpos⟩⟩
    · exact ⟨0, fun h => (hz h).elim⟩
  choose F hF using hexz
  let G : ((ExtRanking m → ℝ) × ℝ) → (Ranking m → ℝ) := fun z => if z ∈ U then F z else 0
  have hGF {z : (ExtRanking m → ℝ) × ℝ} (hz : z ∈ U) : G z = F z := if_pos hz
  have hG {z : (ExtRanking m → ℝ) × ℝ} (hz : z ∈ U) :
      IsCommonJunction g (G z) ∧ (∀ s : ExtRanking m, G z s.1 = z.1 s) ∧
        cycTotal (G z) = z.2 ∧ ∀ r, 1 < G z r := by
    rw [hGF hz]
    exact hF z hz
  have hUopen : IsOpen U := by
    exact (isOpen_set_pi Set.finite_univ fun s _ => isOpen_Ioo).prod isOpen_Ioo
  refine ⟨a, b, T, T + 1, U, L, G, ?_, by linarith, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s
    dsimp [a, b]
    norm_num
  · apply LipschitzOnWith.of_dist_le_mul
    intro z hz w hw
    have hp := hLip₀ (G z) (G w) (hG hz).1 (hG hw).1 (hG hz).2.2.2 (hG hw).2.2.2
      (fun s => by rw [(hG hz).2.1 s]; exact (hbox hz).1 s |>.2)
      (fun s => by rw [(hG hw).2.1 s]; exact (hbox hw).1 s |>.2)
    calc
      dist (G z) (G w) ≤ (L : ℝ) *
          max (‖fun s : ExtRanking m => G z s.1 - G w s.1‖) |cycTotal (G z) - cycTotal (G w)| := hp
      _ = (L : ℝ) * dist z w := by
        rw [Prod.dist_eq, (hG hz).2.2.1, (hG hw).2.2.1, Real.dist_eq]
        congr 2
        · rw [dist_eq_norm]
          congr 1
          funext s
          rw [(hG hz).2.1 s, (hG hw).2.1 s]
          rfl
  · intro z hz
    exact ⟨(hG hz).2.1, (hG hz).2.2.1⟩
  · intro z hz
    exact (hG hz).1
  · intro z hz P hP hPe hPτ
    have hp := hLip₀ P (G z) hP (hG hz).1 (hpos_of hz hP hPe hPτ) (hG hz).2.2.2
      (fun s => by rw [hPe s]; exact (hbox hz).1 s |>.2)
      (fun s => by rw [(hG hz).2.1 s]; exact (hbox hz).1 s |>.2)
    have he : (fun s : ExtRanking m => P s.1 - G z s.1) = 0 := by
      funext s
      rw [hPe s, (hG hz).2.1 s, sub_self]
      rfl
    have ht : cycTotal P - cycTotal (G z) = 0 := by rw [hPτ, (hG hz).2.2.1, sub_self]
    rw [he, ht] at hp
    simp only [norm_zero, abs_zero, max_self, mul_zero] at hp
    exact dist_eq_zero.mp (le_antisymm hp dist_nonneg)
  · intro z hz r
    exact (hG hz).2.2.2 r
  · exact proposition_6_11_rank U hUopen G (fun z hz => ⟨(hG hz).2.1, (hG hz).2.2.1⟩)
