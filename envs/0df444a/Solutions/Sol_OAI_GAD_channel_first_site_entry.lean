-- Prove2me | solution 1 for OAI.GAD.channel_first_site_entry
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:03:12.315114+00:00
-- url     : https://prove2.me/submissions/a23358ff-4c33-4b62-b91c-af376415ae51

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/PureRecursion.lean:L171-L198
-- (upload_full_project.md Phase 4): solution for node OAI.GAD.channel_first_site_entry. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AmplitudeDamping
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Channel
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_MatrixDifferentiation
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetConvexity
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Pinching
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_GramMatrices
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_ScalarDeficit
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_ThermalEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_OutputConvexity
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_TensorEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_PureRecursion

-- ---- from OAI.InformationTheory.AmplitudeDamping.Channel ----
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23

section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

theorem sum_fin_cons {α : Type u_1} {M : Type u_2} [Fintype α] [AddCommMonoid M] {n : ℕ}
    (f : (Fin (n+1) → α) → M) :
    ∑ r, f r = ∑ a, ∑ r : Fin n → α, f (Fin.cons a r) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) ↦ α)).sum_comp f]
  rw [Fintype.sum_prod_type]
  rfl

end GAD

end

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

theorem mul_pure_mul_conjTranspose {ι : Type u_13} {κ : Type u_14} [Fintype κ]
    (L : Matrix ι κ ℂ) (ψ : κ → ℂ) : L * pure ψ * L.conjTranspose = pure (L *ᵥ ψ) := by
  change L * Matrix.vecMulVec ψ (star ψ) * L.conjTranspose =
    Matrix.vecMulVec (L *ᵥ ψ) (star (L *ᵥ ψ))
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ← Matrix.star_mulVec]

end GAD

end

end OAI

-- ---- from OAI.InformationTheory.AmplitudeDamping.PureRecursion ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4

namespace GAD

section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
variable {ι : Type u_1} [Fintype ι]

variable [DecidableEq ι]

end

section
open scoped BigOperators ComplexOrder
open Matrix

end

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix

theorem channel_pure_apply (γ ν : ℝ) (n : ℕ) (ψ : Basis n → ℂ) (i j : Basis n) :
    channel γ ν n (pure ψ) i j =
      ∑ r, (tensorKraus γ ν n r *ᵥ ψ) i * star ((tensorKraus γ ν n r *ᵥ ψ) j) := by
  simp only [channel,mul_pure_mul_conjTranspose,Matrix.sum_apply,pure]

theorem tensorKraus_mulVec_cons (γ ν : ℝ) {n : ℕ} (r : Fin 4) (R : Fin n → Fin 4)
    (ψ : Basis (n+1) → ℂ) (b : Fin 2) (i : Basis n) :
    (tensorKraus γ ν (n+1) (Fin.cons r R) *ᵥ ψ) (Fin.cons b i) =
      ∑ a : Fin 2, kraus γ ν r b a * (tensorKraus γ ν n R *ᵥ branch ψ a) i := by
  simp only [Matrix.mulVec,dotProduct]
  rw [sum_fin_cons]
  simp only [tensorKraus,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ]
  simp only [branch,Finset.mul_sum,mul_assoc]

theorem channel_first_site_entry (γ ν : ℝ) {n : ℕ} (ψ : Basis (n+1) → ℂ)
    (b c : Fin 2) (i j : Basis n) :
    channel γ ν (n+1) (pure ψ) (Fin.cons b i) (Fin.cons c j) =
      applyKraus (kraus γ ν)
        (fun a d ↦ (columns (tensorKraus γ ν n) (branch ψ a) *
          (columns (tensorKraus γ ν n) (branch ψ d)).conjTranspose) i j) b c := by
  rw [channel_pure_apply,sum_fin_cons]
  simp only [tensorKraus_mulVec_cons]
  let u (R : Fin n → Fin 4) (a : Fin 2) (k : Basis n) :=
    (tensorKraus γ ν n R *ᵥ branch ψ a) k
  change (∑ r : Fin 4, ∑ R : Fin n → Fin 4,
      (∑ a : Fin 2, kraus γ ν r b a * u R a i) *
        star (∑ d : Fin 2, kraus γ ν r c d * u R d j)) =
    ∑ r : Fin 4, ∑ d : Fin 2,
      (∑ a : Fin 2, kraus γ ν r b a * (∑ R : Fin n → Fin 4, u R a i * star (u R d j))) *
        star (kraus γ ν r c d)
  simp only [star_sum,star_mul,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro R _
  ring

end GAD

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

variable {ι : Type u_2} {κ : Type u_3} {ρ : Type u_4} [Fintype ι] [Fintype κ] [Fintype ρ]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq ρ]

end GAD

end

end OAI

-- ---- platform node ----
open OAI OAI.GAD
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix


theorem solution : type_of% @_root_.OAI.GAD.channel_first_site_entry := @_root_.OAI.GAD.channel_first_site_entry
