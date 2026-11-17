-- Prove2me | solution 1 for KnodelPrimeCordial.incident_edge_label_repr__p2m_df77e916_fdac_4de2_9395_a46d11d6721f_a1
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-16T12:53:27.358733+00:00
-- url     : https://prove2.me/submissions/8928b235-c582-41de-8ba9-b2095e2152cd

import Mathlib
import Definitions.Def_KnodelPrimeCordial_IsPrimeCordialLabeling

theorem solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (f : V → ℕ) (hbij : Set.BijOn f Set.univ (Set.Icc 1 8))
    (e : Sym2 V) (he : e ∈ G.edgeFinset) (v : V) (hv : v ∈ e) :
    ∃ w : V, KnodelPrimeCordial.edgeGcd f e = Nat.gcd (f v) (f w) ∧
      f v ≠ f w ∧ f w ∈ Set.Icc 1 8 := by
  refine ⟨Sym2.Mem.other' hv, ?_, ?_, ?_⟩
  · have hrepr : e = Sym2.mk v (Sym2.Mem.other' hv) :=
      (Sym2.other_spec' hv).symm
    calc
      KnodelPrimeCordial.edgeGcd f e =
          KnodelPrimeCordial.edgeGcd f (Sym2.mk v (Sym2.Mem.other' hv)) :=
        congrArg (KnodelPrimeCordial.edgeGcd f) hrepr
      _ = Nat.gcd (f v) (f (Sym2.Mem.other' hv)) := by
        simp only [KnodelPrimeCordial.edgeGcd, Sym2.lift_mk]
  · have hne' : Sym2.Mem.other hv ≠ v :=
      G.edge_other_ne (SimpleGraph.mem_edgeFinset.mp he) hv
    have hne : Sym2.Mem.other' hv ≠ v := by
      intro h
      exact hne' ((Sym2.other_eq_other' hv).trans h)
    intro hlabels
    apply hne
    exact (hbij.injOn (by simp) (by simp) hlabels).symm
  · exact hbij.mapsTo (by simp)
