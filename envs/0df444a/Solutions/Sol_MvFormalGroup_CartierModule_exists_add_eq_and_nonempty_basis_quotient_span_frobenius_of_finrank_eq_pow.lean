-- Prove2me | solution 1 for MvFormalGroup.CartierModule.exists_add_eq_and_nonempty_basis_quotient_span_frobenius_of_finrank_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/0b6c50be-2a26-501d-98b7-84f23122dcbc

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Theorems.Thm_MvFormalGroup_CartierModule_nonempty_basis_quotient_span_range_map_of_finrank_eq_pow
import Theorems.Thm_MvFormalGroup_CartierModule_nonempty_basis_span_frobenius_of_finite_quotient
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_CartierModule_exists_add_eq_and_nonempty_basis_quotient_span_frobenius_of_finrank_eq_pow
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply"

set_option autoImplicit false

universe u

namespace P2mKcCodimAssembly

open MvFormalGroup MvFormalGroup.CartierModule

theorem isMaximal_span_p (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p] :
    (Ideal.span {(p : WittVector p k)}).IsMaximal := by
  rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp (WittVector.irreducible p)]
  exact IsLocalRing.maximalIdeal.isMaximal _

end P2mKcCodimAssembly

open P2mKcCodimAssembly MvFormalGroup MvFormalGroup.CartierModule in
theorem solution
    (p : ℕ) [Fact p.Prime] {k : Type u} [Field k] [CharP k p] [PerfectRing k p] {d : ℕ}
    (Φ : MvFormalGroup d k) [Φ.IsComm] (h : ℕ)
    (hdeg : Module.finrank k
      (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range (Φ.nthSeries p))) = p ^ h) :
    ∃ e : ℕ, d + e = h ∧
      Nonempty (Module.Basis (Fin e) (WittVector p k ⧸ Ideal.span {(p : WittVector p k)})
        ((MvFormalGroup.CartierModule p Φ ⧸
            (Ideal.span {(p : WittVector p k)} • ⊤ :
              Submodule (WittVector p k) (MvFormalGroup.CartierModule p Φ))) ⧸
          Submodule.span (WittVector p k ⧸ Ideal.span {(p : WittVector p k)})
            (Set.range fun f : MvFormalGroup.CartierModule p Φ =>
              (Submodule.Quotient.mk (MvFormalGroup.CartierModule.frobenius f) :
                MvFormalGroup.CartierModule p Φ ⧸
                  (Ideal.span {(p : WittVector p k)} • ⊤ :
                    Submodule (WittVector p k) (MvFormalGroup.CartierModule p Φ)))))) := by

  haveI := isMaximal_span_p p k
  letI : Field (WittVector p k ⧸ Ideal.span {(p : WittVector p k)}) := Ideal.Quotient.field _

  have hfin : Module.Finite k
      (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range (Φ.nthSeries p))) :=
    Module.finite_of_finrank_pos (by rw [hdeg]; exact pow_pos (Fact.out : p.Prime).pos h)

  set ψ : Φ.Hom Φ := ((p : ℕ) : MvFormalGroup.End Φ) with hψ
  have hψs : ψ.toPowerSeries = Φ.nthSeries p := MvFormalGroup.End.toPowerSeries_natCast (F := Φ) p
  have hdegψ : Module.finrank k
      (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range ψ.toPowerSeries)) = p ^ h := by
    rw [hψs]; exact hdeg

  have hact : ∀ g : CartierModule p Φ, CartierModule.map ψ g = (p : WittVector p k) • g := fun g => by
    rw [natCast_smul_eq_nsmul', ← endAct_natCast]
    rfl
  have hp : ∀ f : CartierModule p Φ, ∃ g : CartierModule p Φ,
      CartierModule.map ψ g = (p : WittVector p k) • f := fun f => ⟨f, hact f⟩

  obtain ⟨bM⟩ := nonempty_basis_quotient_span_range_map_of_finrank_eq_pow p Φ Φ ψ h hdegψ hp

  set Mbar := CartierModule p Φ ⧸ (Ideal.span {(p : WittVector p k)} • ⊤ :
    Submodule (WittVector p k) (CartierModule p Φ)) with hMbar
  set S0 : Submodule (WittVector p k ⧸ Ideal.span {(p : WittVector p k)}) Mbar :=
    Submodule.span (WittVector p k ⧸ Ideal.span {(p : WittVector p k)})
      (Set.range fun g : CartierModule p Φ => (Submodule.Quotient.mk (CartierModule.map ψ g) : Mbar))
    with hS0
  set Fbar : Submodule (WittVector p k ⧸ Ideal.span {(p : WittVector p k)}) Mbar :=
    Submodule.span (WittVector p k ⧸ Ideal.span {(p : WittVector p k)})
      (Set.range fun f : CartierModule p Φ => (Submodule.Quotient.mk (frobenius f) : Mbar)) with hFbar
  have hS0bot : S0 = ⊥ := by
    rw [hS0, Submodule.span_eq_bot]
    rintro _ ⟨g, rfl⟩
    show (Submodule.Quotient.mk (CartierModule.map ψ g) : Mbar) = 0
    rw [hact, Submodule.Quotient.mk_eq_zero, Submodule.ideal_span_singleton_smul]
    exact Submodule.smul_mem_pointwise_smul g (p : WittVector p k) ⊤ Submodule.mem_top

  haveI : Module.Finite (WittVector p k ⧸ Ideal.span {(p : WittVector p k)}) (Mbar ⧸ S0) :=
    Module.Finite.of_basis bM
  haveI : Module.Finite (WittVector p k ⧸ Ideal.span {(p : WittVector p k)}) Mbar :=
    Module.Finite.equiv (Submodule.quotEquivOfEqBot S0 hS0bot)
  have hM : Module.finrank (WittVector p k ⧸ Ideal.span {(p : WittVector p k)}) Mbar = h := by
    rw [← (Submodule.quotEquivOfEqBot S0 hS0bot).finrank_eq, Module.finrank_eq_card_basis bM,
      Fintype.card_fin]
  obtain ⟨bF⟩ := nonempty_basis_span_frobenius_of_finite_quotient p Φ hfin
  have hF : Module.finrank (WittVector p k ⧸ Ideal.span {(p : WittVector p k)}) Fbar = d := by
    rw [Module.finrank_eq_card_basis bF, Fintype.card_fin]
  have hsum := Submodule.finrank_quotient_add_finrank Fbar
  rw [hM, hF] at hsum
  have hq : Module.finrank (WittVector p k ⧸ Ideal.span {(p : WittVector p k)}) (Mbar ⧸ Fbar) = h - d := by
    omega
  exact ⟨h - d, by omega, ⟨Module.finBasisOfFinrankEq _ _ hq⟩⟩

end S_MvFormalGroup_CartierModule_exists_add_eq_and_nonempty_basis_quotient_span_frobenius_of_finrank_eq_pow
end P2MW
export P2MW.S_MvFormalGroup_CartierModule_exists_add_eq_and_nonempty_basis_quotient_span_frobenius_of_finrank_eq_pow (solution)
