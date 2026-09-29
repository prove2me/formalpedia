-- Prove2me | solution 1 for HeckeEis.span_range_coeffH1par_map_int_complex_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/4befc982-9677-5f8f-bb88-7e1db7d40936

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import Theorems.Thm_HeckeEis_exists_basis_coeffH1par_int_complex
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_span_range_coeffH1par_map_int_complex_eq_top

set_option autoImplicit false

namespace HeckeEis
p2m_export "HeckeEis" "BinaryForm binaryFormRepSL coeffParabolicCocycles coeffH1par coeffH1parMk exists_basis_coeffH1par_int_complex"
namespace C2Cor
p2m_open "HeckeEis"

theorem injective_of_bases {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Module ℂ B] {t : ℕ}
    (b : Module.Basis (Fin t) ℤ A) (c : Module.Basis (Fin t) ℂ B) (Φ : A →+ B) (h : ∀ i, c i = Φ (b i)) :
    Function.Injective Φ := by
  classical
  refine (injective_iff_map_eq_zero Φ).mpr fun x hx => ?_
  rw [← b.sum_repr x, map_sum] at hx
  simp only [map_zsmul, ← h] at hx
  have hx' : ∑ i, ((b.repr x i : ℤ) : ℂ) • c i = 0 := by simpa only [Int.cast_smul_eq_zsmul] using hx
  have hc := (linearIndependent_iff'.mp c.linearIndependent) Finset.univ _ hx'
  rw [← b.sum_repr x]
  refine Finset.sum_eq_zero fun i _ => ?_
  have : b.repr x i = 0 := by exact_mod_cast hc i (Finset.mem_univ i)
  rw [this, zero_smul]

theorem span_eq_top_of_bases {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Module ℂ B] {t : ℕ}
    (b : Module.Basis (Fin t) ℤ A) (c : Module.Basis (Fin t) ℂ B) (Φ : A →+ B) (h : ∀ i, c i = Φ (b i)) :
    Submodule.span ℂ (Set.range Φ) = ⊤ := by
  classical
  rw [eq_top_iff]
  intro X _
  rw [← c.sum_repr X]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b i, (h i).symm⟩)

end HeckeEis.C2Cor

open scoped MatrixGroups in

theorem solution (n N : ℕ) [NeZero N]
    (Φ : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype) →+ HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype))
    (hΦ : ∀ z : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
      ∃ w : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
        (∀ g : CongruenceSubgroup.Gamma0 N, ((w : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm ℂ n)) g : MvPolynomial (Fin 2) ℂ)
            = MvPolynomial.map (Int.castRingHom ℂ)
                (((z : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm ℤ n)) g : MvPolynomial (Fin 2) ℤ))) ∧
        Φ (HeckeEis.coeffH1parMk _ z) = HeckeEis.coeffH1parMk _ w) :
    Submodule.span ℂ (Set.range Φ) = ⊤ := by
  obtain ⟨t, b, c, h⟩ := HeckeEis.exists_basis_coeffH1par_int_complex n N Φ hΦ
  exact HeckeEis.C2Cor.span_eq_top_of_bases b c Φ h

#print axioms solution

end S_HeckeEis_span_range_coeffH1par_map_int_complex_eq_top
end P2MW
export P2MW.S_HeckeEis_span_range_coeffH1par_map_int_complex_eq_top (solution)
