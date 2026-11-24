-- Prove2me | solution 1 for GlobalTheory.RootExSource.opE_om_source
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:49:55.322653+00:00
-- url     : https://prove2.me/submissions/d885e8cb-4ba4-43a4-a3a3-c2bd2bf7a795

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SecondCountableLocal
import Theorems.Thm_GlobalTheory_RootExSource_ch_affPt_mul
import Theorems.Thm_GlobalTheory_RootExSource_det_linPart
import Theorems.Thm_GlobalTheory_RootExSource_affPt_mul
import Theorems.Thm_GlobalTheory_RootEx_Radical_unipotent_radical_basic
import Theorems.Thm_GlobalTheory_SplitWeil_linear_change_of_variables

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
noncomputable section
namespace GlobalTheory.RootExSource
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {c p : ℕ}
private theorem secondCountable_local (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : SecondCountableTopology k := by
  let _ := IsTopologicalAddGroup.rightUniformSpace k
  have := isUniformAddGroup_of_addCommGroup (G := k)
  let _ : (Valued.v (R := k)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  open scoped Valued in
  have : ProperSpace k := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace k
  open scoped Valued in
  exact secondCountable_of_proper
end GlobalTheory.RootExSource
end
end

set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
noncomputable section
open GlobalTheory GlobalTheory.RootExSource
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {c p : ℕ}
namespace GlobalTheory.RootExSource
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (_ : 1 ≤ p) (_ : p ≤ c) (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure] (μ : kˣ →* ℂˣ) (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ), ∀ g ∈ N k n' (c + 1) p, opE ψ ν p (om μ g 1 Φ) = (ψ (simpleSum g) : ℂ) • opE ψ ν p Φ := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c p _ _ ψ ν _ μ Φ g hgN
  classical
  have := secondCountable_local k
  obtain ⟨h1, -, h3, -⟩ := GlobalTheory.RootEx.Radical.unipotent_radical_basic k n' (c + 1) p
  have hg : InN p g := (h1 g).1 hgN
  have hdet := h3 g hgN
  have hn1 : nabs k 1 = 1 := by simp [nabs]
  have hom : om μ g 1 Φ = fun x => Φ (x * g.val) := by
    funext x
    simp [om, hdet, hn1]
  funext x₀
  rw [hom, Pi.smul_apply, smul_eq_mul]
  unfold opE
  set v : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k :=
    fun a => (basePt c x₀ * g.val - basePt c x₀) a.1.1 a.1.2 with hv
  set F : ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) → ℂ :=
    fun e => Φ (affPt p x₀ e) * (ψ (-ch (affPt p x₀ e)) : ℂ) with hF
  let G : GL {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} k :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero (linPart n p g) (by rw [det_linPart hg]; exact one_ne_zero)
  have hGval : G.val = linPart n p g := rfl
  have hGdet : Matrix.GeneralLinearGroup.det G = 1 := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, hGval, det_linPart hg]; rfl
  have hcov := (GlobalTheory.SplitWeil.linear_change_of_variables k {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} n ν).1 G
    (fun e => F (e + v))
  rw [hGdet, hn1, inv_one, one_smul, hGval] at hcov
  have hint : ∀ e, Φ (affPt p x₀ e * g.val) * (ψ (-ch (affPt p x₀ e)) : ℂ) =
      (ψ (simpleSum g) : ℂ) * F ((linPart n p g).mulVec e + v) := by
    intro e
    simp only [hF]
    rw [hv, ← affPt_mul hg, ch_affPt_mul hg, mul_left_comm, ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
    congr 3
    ring
  simp only [hint]
  rw [integral_const_mul, hcov]
  congr 1
  exact integral_add_right_eq_self F v
end GlobalTheory.RootExSource
