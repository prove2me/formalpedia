-- Prove2me | solution 1 for OAI.Kadison.unitary_dihedral
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:09:47.264107+00:00
-- url     : https://prove2.me/submissions/092e8012-6432-46d5-844b-31b60c71aef5

import Mathlib

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixColumnCorner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder Matrix.Norms.L2Operator

namespace Kadison

variable {A : Type*} [CStarAlgebra A] {p : A} (hp : IsStarProjection p)

include hp

omit hp in
lemma unitary_dihedral_oai {d s : unitary A} (hd : (d:A)*(d:A)=1) (hs : (s:A)*(s:A)=1) :
    MulAut.conj d (d*s)=(d*s)⁻¹ := by
  have hd' : d*d=1 := Subtype.ext hd
  have hs' : s*s=1 := Subtype.ext hs
  have hdi : d⁻¹=d := inv_eq_of_mul_eq_one_right hd'
  have hsi : s⁻¹=s := inv_eq_of_mul_eq_one_right hs'
  simp only [MulAut.conj_apply,mul_inv_rev,hdi,hsi]
  rw [←mul_assoc,hd',one_mul]

end Kadison

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.unitary_dihedral_oai.{u_1} := @OAI.Kadison.unitary_dihedral_oai.{u_1}
