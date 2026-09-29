-- Prove2me | solution 1 for LanglandsTunnell.TateLocal.psiLocal_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/8b7c12c8-ba43-5be1-a09a-8fd974778cbb

import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Theorems.Thm_NumberField_StandardAddChar_psiLocal_eq_psiLocal_trace
import Theorems.Thm_NumberField_StandardAddChar_psiLocal_rat_eq_psiV
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_TateLocal_psiLocal_ne_one

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell
namespace TateLocal
namespace SolED33
p2m_open "LanglandsTunnell.TateLocal LanglandsTunnell"

open NumberField IsDedekindDomain NumberField.StandardAddChar

private theorem trace_surjective (p : HeightOneSpectrum (𝓞 ℚ)) {K : Type} [Field K] [NumberField K]
    (w : p.Extension (𝓞 K)) :
    Function.Surjective
      (Algebra.trace (p.adicCompletion ℚ) (w.1.adicCompletion K)) := by
  intro c
  haveI : CharZero (p.adicCompletion ℚ) :=
    charZero_of_injective_algebraMap (algebraMap ℚ (p.adicCompletion ℚ)).injective
  have hn : (Module.finrank (p.adicCompletion ℚ) (w.1.adicCompletion K) :
      p.adicCompletion ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  refine ⟨algebraMap (p.adicCompletion ℚ) (w.1.adicCompletion K)
    (c / (Module.finrank (p.adicCompletion ℚ) (w.1.adicCompletion K) :
      p.adicCompletion ℚ)), ?_⟩
  rw [Algebra.trace_algebraMap, nsmul_eq_mul, mul_comm, div_mul_cancel₀ _ hn]

private theorem main_of_dock_of_base {K : Type} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K))
    (p : HeightOneSpectrum (𝓞 ℚ)) (w : p.Extension (𝓞 K)) (hw : w.1 = v)
    (hdock : ∀ x : w.1.adicCompletion K,
      psiLocal K w.1 x
        = psiLocal ℚ p (Algebra.trace (p.adicCompletion ℚ) (w.1.adicCompletion K) x))
    (hbase : psiLocal ℚ p ≠ 1) :
    psiLocal K v ≠ 1 := by
  subst hw
  intro htriv
  apply hbase
  ext y
  obtain ⟨x, hx⟩ := trace_surjective p w y
  have := hdock x
  rw [htriv] at this
  simp only [AddChar.one_apply] at this
  rw [AddChar.one_apply, ← hx, ← this]

private theorem main_of_docks {K : Type} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K))
    (p : HeightOneSpectrum (𝓞 ℚ)) (w : p.Extension (𝓞 K)) (hw : w.1 = v)
    (hdock : ∀ x : w.1.adicCompletion K,
      psiLocal K w.1 x
        = psiLocal ℚ p (Algebra.trace (p.adicCompletion ℚ) (w.1.adicCompletion K) x))
    (hR2 : psiLocal ℚ p = psiV p) :
    psiLocal K v ≠ 1 :=
  main_of_dock_of_base v p w hw hdock
    (fun h => psiV_algebraMap_inv_ne_one p (by rw [← hR2, h]; rfl))

end LanglandsTunnell.TateLocal.SolED33

end

theorem solution (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    NumberField.StandardAddChar.psiLocal K v ≠ 1 :=
  LanglandsTunnell.TateLocal.SolED33.main_of_docks v
    (v.under (NumberField.RingOfIntegers ℚ)) ⟨v, rfl⟩ rfl
    (NumberField.StandardAddChar.psiLocal_eq_psiLocal_trace ℚ K
      (v.under (NumberField.RingOfIntegers ℚ)) ⟨v, rfl⟩)
    (NumberField.StandardAddChar.psiLocal_rat_eq_psiV
      (v.under (NumberField.RingOfIntegers ℚ)))

end S_LanglandsTunnell_TateLocal_psiLocal_ne_one
end P2MW
export P2MW.S_LanglandsTunnell_TateLocal_psiLocal_ne_one (solution)
