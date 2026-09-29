-- Prove2me | solution 1 for MvFormalGroup.CartierModule.nonempty_basis_quotient_smul_top_of_finrank_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/00f9c4b6-ffb4-580d-90ad-1ce20539d383

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Theorems.Thm_MvFormalGroup_CartierModule_nonempty_basis_span_frobenius_of_finite_quotient
import Theorems.Thm_MvFormalGroup_CartierModule_exists_add_eq_and_nonempty_basis_quotient_span_frobenius_of_finrank_eq_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_CartierModule_nonempty_basis_quotient_smul_top_of_finrank_eq_pow
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply"

set_option autoImplicit false

universe u

namespace P2mKcHeightRankAssembly

theorem isMaximal_span_p (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p] :
    (Ideal.span {(p : WittVector p k)}).IsMaximal := by
  rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp (WittVector.irreducible p)]
  exact IsLocalRing.maximalIdeal.isMaximal _

end P2mKcHeightRankAssembly

open P2mKcHeightRankAssembly MvFormalGroup MvFormalGroup.CartierModule in
theorem solution
    (p : ℕ) [Fact p.Prime] {k : Type u} [Field k] [CharP k p] [PerfectRing k p] {d : ℕ}
    (Φ : MvFormalGroup d k) [Φ.IsComm] (h : ℕ)
    (hdeg : Module.finrank k
      (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range (Φ.nthSeries p))) = p ^ h) :
    Nonempty (Module.Basis (Fin h) (WittVector p k ⧸ Ideal.span {(p : WittVector p k)})
      (MvFormalGroup.CartierModule p Φ ⧸
        (Ideal.span {(p : WittVector p k)} • ⊤ :
          Submodule (WittVector p k) (MvFormalGroup.CartierModule p Φ)))) := by

  have hfin : Module.Finite k
      (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range (Φ.nthSeries p))) :=
    Module.finite_of_finrank_pos (by rw [hdeg]; exact pow_pos (Fact.out : p.Prime).pos h)

  haveI := isMaximal_span_p p k
  letI : Field (WittVector p k ⧸ Ideal.span {(p : WittVector p k)}) := Ideal.Quotient.field _

  obtain ⟨bF⟩ := nonempty_basis_span_frobenius_of_finite_quotient p Φ hfin
  obtain ⟨e, hde, ⟨bQ⟩⟩ :=
    exists_add_eq_and_nonempty_basis_quotient_span_frobenius_of_finrank_eq_pow p Φ h hdeg

  set Fbar := Submodule.span (WittVector p k ⧸ Ideal.span {(p : WittVector p k)})
    (Set.range fun f : CartierModule p Φ =>
      (Submodule.Quotient.mk (frobenius f) : CartierModule p Φ ⧸
        (Ideal.span {(p : WittVector p k)} • ⊤ :
          Submodule (WittVector p k) (CartierModule p Φ)))) with hFbar
  haveI : Module.Finite (WittVector p k ⧸ Ideal.span {(p : WittVector p k)}) Fbar :=
    Module.Finite.of_basis bF
  haveI : Module.Finite (WittVector p k ⧸ Ideal.span {(p : WittVector p k)})
      ((CartierModule p Φ ⧸ (Ideal.span {(p : WittVector p k)} • ⊤ :
        Submodule (WittVector p k) (CartierModule p Φ))) ⧸ Fbar) :=
    Module.Finite.of_basis bQ
  haveI : Module.Finite (WittVector p k ⧸ Ideal.span {(p : WittVector p k)})
      (CartierModule p Φ ⧸ (Ideal.span {(p : WittVector p k)} • ⊤ :
        Submodule (WittVector p k) (CartierModule p Φ))) :=
    Module.Finite.of_submodule_quotient Fbar
  have hrank : Module.finrank (WittVector p k ⧸ Ideal.span {(p : WittVector p k)})
      (CartierModule p Φ ⧸ (Ideal.span {(p : WittVector p k)} • ⊤ :
        Submodule (WittVector p k) (CartierModule p Φ))) = h := by
    rw [← Submodule.finrank_quotient_add_finrank Fbar, Module.finrank_eq_card_basis bQ,
      Module.finrank_eq_card_basis bF, Fintype.card_fin, Fintype.card_fin, ← hde, add_comm]
  exact ⟨Module.finBasisOfFinrankEq _ _ hrank⟩

end S_MvFormalGroup_CartierModule_nonempty_basis_quotient_smul_top_of_finrank_eq_pow
end P2MW
export P2MW.S_MvFormalGroup_CartierModule_nonempty_basis_quotient_smul_top_of_finrank_eq_pow (solution)
