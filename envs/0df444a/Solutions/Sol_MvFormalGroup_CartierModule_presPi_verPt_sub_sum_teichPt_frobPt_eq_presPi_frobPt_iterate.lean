-- Prove2me | solution 1 for MvFormalGroup.CartierModule.presPi_verPt_sub_sum_teichPt_frobPt_eq_presPi_frobPt_iterate
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/5b392d89-f628-5355-9715-8b4ec88ffa3a

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_WittPointFamily
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_CartierModule_presPi_verPt_sub_sum_teichPt_frobPt_eq_presPi_frobPt_iterate

set_option autoImplicit false

universe u v

noncomputable section

namespace P2mKcKappaOne

open MvFormalGroup MvFormalGroup.CartierModule

variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] [CharP R p] {d : ℕ}
  {Φ : MvFormalGroup d R} [Φ.IsComm] {τ : Type v}

theorem verschiebung_iterate_sum {ι : Type*} (s : Finset ι) (g : ι → CartierModule p Φ) (m : ℕ) :
    (⇑(verschiebung (p := p) (Φ := Φ)))^[m] (∑ l ∈ s, g l) =
      ∑ l ∈ s, (⇑(verschiebung (p := p) (Φ := Φ)))^[m] (g l) := by
  induction m with
  | zero => simp only [Function.iterate_zero, id_eq]
  | succ m ih => simp only [Function.iterate_succ_apply', ih, map_sum]

omit [CharP R p] in

theorem evalPt_sum_apply {ι : Type*} (s : Finset ι) (g : ι → CartierModule p Φ)
    (w : WittLaw.seriesPoint p R τ) :
    evalPt (∑ l ∈ s, g l) w = ∑ l ∈ s, evalPt (g l) w := by
  rw [map_sum, AddMonoidHom.finsetSum_apply]

theorem evalPt_frobenius_of_expansion
    (f : Fin d → CartierModule p Φ) (N : ℕ) (c : Fin N → Fin d → Fin d → R)
    (h : Fin d → CartierModule p Φ)
    (hexp : ∀ i, frobenius (f i) =
      (∑ m : Fin N, (⇑(verschiebung (p := p) (Φ := Φ)))^[m] (∑ l : Fin d, homothety (c m i l) (f l))) +
        (⇑(verschiebung (p := p) (Φ := Φ)))^[N] (h i))
    (i : Fin d) (w : WittLaw.seriesPoint p R τ) :
    evalPt (frobenius (f i)) w =
      (∑ m : Fin N, ∑ l : Fin d,
          evalPt ((⇑(verschiebung (p := p) (Φ := Φ)))^[m] (homothety (c m i l) (f l))) w) +
        evalPt ((⇑(verschiebung (p := p) (Φ := Φ)))^[N] (h i)) w := by
  rw [hexp i, map_add, AddMonoidHom.add_apply, evalPt_sum_apply]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [verschiebung_iterate_sum, evalPt_sum_apply]

end P2mKcKappaOne

end

open MvFormalGroup MvFormalGroup.CartierModule P2mKcKappaOne in
theorem solution
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] [CharP R p] {d : ℕ}
    (Φ : MvFormalGroup d R) [Φ.IsComm]
    (f : Fin d → MvFormalGroup.CartierModule p Φ) (N : ℕ) (c : Fin N → Fin d → Fin d → R)
    (h : Fin d → MvFormalGroup.CartierModule p Φ)
    (hexp : ∀ i, MvFormalGroup.CartierModule.frobenius (f i) =
      (∑ m : Fin N, (⇑(MvFormalGroup.CartierModule.verschiebung (p := p) (Φ := Φ)))^[m]
          (∑ l : Fin d, MvFormalGroup.CartierModule.homothety (c m i l) (f l))) +
        (⇑(MvFormalGroup.CartierModule.verschiebung (p := p) (Φ := Φ)))^[N] (h i))
    {τ : Type v} (u : Fin d → MvFormalGroup.WittLaw.seriesPoint p R τ) :
    MvFormalGroup.CartierModule.presPi f
        (fun l => MvFormalGroup.WittLaw.verPt (u l) -
          ∑ i : Fin d, ∑ m : Fin N, MvFormalGroup.WittLaw.teichPt (c m i l)
            ((⇑(MvFormalGroup.WittLaw.frobPt (p := p) (R := R) (τ := τ)))^[m] (u i))) =
      MvFormalGroup.CartierModule.presPi h
        (fun i => (⇑(MvFormalGroup.WittLaw.frobPt (p := p) (R := R) (τ := τ)))^[N] (u i)) := by

  simp only [presPi_def, map_sub, map_sum, evalPt_verPt, evalPt_teichPt, evalPt_frobPt_iterate]
  have hF : (∑ l : Fin d, evalPt (frobenius (f l)) (u l)) =
      ∑ i : Fin d, ((∑ m : Fin N, ∑ l : Fin d,
          evalPt ((⇑(verschiebung (p := p) (Φ := Φ)))^[m] (homothety (c m i l) (f l))) (u i)) +
        evalPt ((⇑(verschiebung (p := p) (Φ := Φ)))^[N] (h i)) (u i)) :=
    Finset.sum_congr rfl fun i _ => evalPt_frobenius_of_expansion f N c h hexp i (u i)
  rw [Finset.sum_sub_distrib, hF, Finset.sum_add_distrib]
  have hswap :
      (∑ i : Fin d, ∑ m : Fin N, ∑ l : Fin d,
          evalPt ((⇑(verschiebung (p := p) (Φ := Φ)))^[m] (homothety (c m i l) (f l))) (u i)) =
        ∑ l : Fin d, ∑ i : Fin d, ∑ m : Fin N,
          evalPt ((⇑(verschiebung (p := p) (Φ := Φ)))^[m] (homothety (c m i l) (f l))) (u i) :=
    calc (∑ i : Fin d, ∑ m : Fin N, ∑ l : Fin d,
            evalPt ((⇑(verschiebung (p := p) (Φ := Φ)))^[m] (homothety (c m i l) (f l))) (u i))
        = ∑ i : Fin d, ∑ l : Fin d, ∑ m : Fin N,
            evalPt ((⇑(verschiebung (p := p) (Φ := Φ)))^[m] (homothety (c m i l) (f l))) (u i) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ l : Fin d, ∑ i : Fin d, ∑ m : Fin N,
            evalPt ((⇑(verschiebung (p := p) (Φ := Φ)))^[m] (homothety (c m i l) (f l))) (u i) :=
          Finset.sum_comm
  rw [hswap, add_sub_cancel_left]

end S_MvFormalGroup_CartierModule_presPi_verPt_sub_sum_teichPt_frobPt_eq_presPi_frobPt_iterate
end P2MW
export P2MW.S_MvFormalGroup_CartierModule_presPi_verPt_sub_sum_teichPt_frobPt_eq_presPi_frobPt_iterate (solution)
