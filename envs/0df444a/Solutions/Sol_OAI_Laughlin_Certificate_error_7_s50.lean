-- Prove2me | solution 1 for OAI.Laughlin.Certificate.error_7_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T12:45:13.604605+00:00
-- url     : https://prove2.me/submissions/9a22e7a7-969f-4024-8591-8ea170a72bfc

import Mathlib
import Definitions.Def_OAIQ050L010
import Theorems.Thm_OAI_Laughlin_Certificate_error_7_3_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_error_7_5_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_error_7_5_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_error_7_7_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_error_7_7_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_error_7_7_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_error_7_7_7_s50

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
open scoped BigOperators Matrix

theorem Y_expand (D r s : ℕ) : Y D r s =
    -(yRow D r s (rows[0]!) + (yRow D r s (rows[1]!) +
      (yRow D r s (rows[2]!) + (yRow D r s (rows[3]!) +
        (yRow D r s (rows[4]!) + (yRow D r s (rows[5]!) +
          (yRow D r s (rows[6]!) + 0))))))) / (10^14 : ℚ) := by rfl

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_Row07
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem yRow_7_1_1_0 : yRow 7 1 1 (rows[0]!) = (7813395192175504245 / 4096 : ℚ) := by
  decide +kernel

theorem yRow_7_1_1_1 : yRow 7 1 1 (rows[1]!) = (36323988982144322139 / 67108864 : ℚ) := by
  decide +kernel

theorem yRow_7_1_1_2 : yRow 7 1 1 (rows[2]!) = (56489461722547816265955 / 268435456 : ℚ) := by
  decide +kernel

theorem yRow_7_1_1_3 : yRow 7 1 1 (rows[3]!) = (-181450975756044921243195 / 469762048 : ℚ) := by
  decide +kernel

theorem yRow_7_1_1_4 : yRow 7 1 1 (rows[4]!) = (-2508628320709374018255 / 29360128 : ℚ) := by
  decide +kernel

theorem yRow_7_1_1_5 : yRow 7 1 1 (rows[5]!) = (1591029590813751708821385 / 1879048192 : ℚ) := by
  decide +kernel

theorem yRow_7_1_1_6 : yRow 7 1 1 (rows[6]!) = (-4276885373741756719485 / 33554432 : ℚ) := by
  decide +kernel

theorem yRow_7_1_3_0 : yRow 7 1 3 (rows[0]!) = (-3670890702116855625 / 8192 : ℚ) := by
  decide +kernel

theorem yRow_7_1_3_1 : yRow 7 1 3 (rows[1]!) = (-28502538608116390869 / 33554432 : ℚ) := by
  decide +kernel

theorem yRow_7_1_3_2 : yRow 7 1 3 (rows[2]!) = (2988849553778345597235 / 134217728 : ℚ) := by
  decide +kernel

theorem yRow_7_1_3_3 : yRow 7 1 3 (rows[3]!) = (-12918373159386147536445 / 234881024 : ℚ) := by
  decide +kernel

theorem yRow_7_1_3_4 : yRow 7 1 3 (rows[4]!) = (3528819936117742548165 / 58720256 : ℚ) := by
  decide +kernel

theorem yRow_7_1_3_5 : yRow 7 1 3 (rows[5]!) = (-29217720453316236095145 / 939524096 : ℚ) := by
  decide +kernel

theorem yRow_7_1_3_6 : yRow 7 1 3 (rows[6]!) = (-76772184534764046045 / 8388608 : ℚ) := by
  decide +kernel

theorem yRow_7_1_5_0 : yRow 7 1 5 (rows[0]!) = (205314913297683315 / 256 : ℚ) := by
  decide +kernel

theorem yRow_7_1_5_1 : yRow 7 1 5 (rows[1]!) = (-2180568515710116549 / 16777216 : ℚ) := by
  decide +kernel

theorem yRow_7_1_5_2 : yRow 7 1 5 (rows[2]!) = (50011870045872224797155 / 67108864 : ℚ) := by
  decide +kernel

theorem yRow_7_1_5_3 : yRow 7 1 5 (rows[3]!) = (126559883614713029393025 / 117440512 : ℚ) := by
  decide +kernel

theorem yRow_7_1_5_4 : yRow 7 1 5 (rows[4]!) = (-46679206856806148273295 / 469762048 : ℚ) := by
  decide +kernel

theorem yRow_7_1_5_5 : yRow 7 1 5 (rows[5]!) = (486363383031076447124835 / 1879048192 : ℚ) := by
  decide +kernel

theorem yRow_7_1_5_6 : yRow 7 1 5 (rows[6]!) = (-620279821822140423225 / 33554432 : ℚ) := by
  decide +kernel

theorem yRow_7_1_7_0 : yRow 7 1 7 (rows[0]!) = (15514482988745341335 / 2048 : ℚ) := by
  decide +kernel

theorem yRow_7_1_7_1 : yRow 7 1 7 (rows[1]!) = (34459028886161906571 / 8388608 : ℚ) := by
  decide +kernel

theorem yRow_7_1_7_2 : yRow 7 1 7 (rows[2]!) = (207794480500460556638835 / 33554432 : ℚ) := by
  decide +kernel

theorem yRow_7_1_7_3 : yRow 7 1 7 (rows[3]!) = (-12487246647748499348535 / 8388608 : ℚ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_Fast
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem yEntry_eq_fast (D r s t : ℕ) (e f : ℕ × ℕ × ℤ) :
    yEntry D r s t e f = yEntryFast D r s t e f := by
  rcases e with ⟨p,j,a⟩
  rcases f with ⟨q,l,b⟩
  dsimp [yEntry, yEntryFast]
  split_ifs with hD hz
  · rcases hz with hz | hz <;> simp [hz]
  · push_cast
    ring
  · rfl

theorem yRow_eq_fast (D r s : ℕ) (row : ℕ × ℤ × List (ℕ × ℕ × ℤ)) :
    yRow D r s row = yRowFast D r s row := by
  simp only [yRow, yRowFast, yEntry_eq_fast]

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_Row072
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem yRow_7_1_7_4 : yRow 7 1 7 (rows[4]!) = (20867558445854020401465 / 33554432 : ℚ) := by
  rw [yRow_eq_fast]
  decide +kernel

theorem yRow_7_1_7_5 : yRow 7 1 7 (rows[5]!) = (-87026179675834894580205 / 134217728 : ℚ) := by
  rw [yRow_eq_fast]
  decide +kernel

theorem yRow_7_1_7_6 : yRow 7 1 7 (rows[6]!) = (201099333031028464725 / 4194304 : ℚ) := by
  rw [yRow_eq_fast]
  decide +kernel

theorem yRow_7_3_3_0 : yRow 7 3 3 (rows[0]!) = (1339467956678017935 / 8192 : ℚ) := by
  rw [yRow_eq_fast]
  decide +kernel

theorem yRow_7_3_3_1 : yRow 7 3 3 (rows[1]!) = (6048833004624160083 / 16777216 : ℚ) := by
  rw [yRow_eq_fast]
  decide +kernel

theorem yRow_7_3_3_2 : yRow 7 3 3 (rows[2]!) = (21081146259965870818659 / 67108864 : ℚ) := by
  rw [yRow_eq_fast]
  decide +kernel

theorem yRow_7_3_3_3 : yRow 7 3 3 (rows[3]!) = (11539020213471479679117 / 117440512 : ℚ) := by
  rw [yRow_eq_fast]
  decide +kernel

theorem yRow_7_3_3_4 : yRow 7 3 3 (rows[4]!) = (5238129656277557731281 / 234881024 : ℚ) := by
  rw [yRow_eq_fast]
  decide +kernel

theorem yRow_7_3_3_5 : yRow 7 3 3 (rows[5]!) = (44738130881813395918293 / 234881024 : ℚ) := by
  rw [yRow_eq_fast]
  decide +kernel

theorem yRow_7_3_3_6 : yRow 7 3 3 (rows[6]!) = (-61880973868094171805 / 8388608 : ℚ) := by
  rw [yRow_eq_fast]
  decide +kernel

theorem yRow_7_3_5_0 : yRow 7 3 5 (rows[0]!) = (11065428419616135 / 1024 : ℚ) := by
  rw [yRow_eq_fast]
  decide +kernel

theorem yRow_7_3_5_1 : yRow 7 3 5 (rows[1]!) = (2141394541249492635 / 8388608 : ℚ) := by
  rw [yRow_eq_fast]
  decide +kernel

theorem yRow_7_3_5_2 : yRow 7 3 5 (rows[2]!) = (-23803270741598517863565 / 33554432 : ℚ) := by
  rw [yRow_eq_fast]
  decide +kernel

theorem yRow_7_3_5_3 : yRow 7 3 5 (rows[3]!) = (-14416679890174213591545 / 58720256 : ℚ) := by
  rw [yRow_eq_fast]
  decide +kernel

theorem yRow_7_3_5_4 : yRow 7 3 5 (rows[4]!) = (-54234982718013152865 / 7340032 : ℚ) := by
  rw [yRow_eq_fast]
  decide +kernel

theorem yRow_7_3_5_5 : yRow 7 3 5 (rows[5]!) = (310146766753353391486215 / 939524096 : ℚ) := by
  rw [yRow_eq_fast]
  decide +kernel

theorem yRow_7_3_5_6 : yRow 7 3 5 (rows[6]!) = (-50552514240995949885 / 16777216 : ℚ) := by
  rw [yRow_eq_fast]
  decide +kernel

theorem yRow_7_3_7_0 : yRow 7 3 7 (rows[0]!) = (-1488415248143087355 / 2048 : ℚ) := by
  rw [yRow_eq_fast]
  decide +kernel

theorem yRow_7_3_7_1 : yRow 7 3 7 (rows[1]!) = (9225871950243624195 / 4194304 : ℚ) := by
  rw [yRow_eq_fast]
  decide +kernel

theorem yRow_7_3_7_2 : yRow 7 3 7 (rows[2]!) = (-3990280684502974026525 / 16777216 : ℚ) := by
  rw [yRow_eq_fast]
  decide +kernel

theorem yRow_7_3_7_3 : yRow 7 3 7 (rows[3]!) = (-6304209573025048032825 / 4194304 : ℚ) := by
  rw [yRow_eq_fast]
  decide +kernel

theorem yRow_7_3_7_4 : yRow 7 3 7 (rows[4]!) = (-1462389462807293524305 / 8388608 : ℚ) := by
  rw [yRow_eq_fast]
  decide +kernel

theorem yRow_7_3_7_5 : yRow 7 3 7 (rows[5]!) = (51986196748062068309475 / 67108864 : ℚ) := by
  rw [yRow_eq_fast]
  decide +kernel

theorem yRow_7_3_7_6 : yRow 7 3 7 (rows[6]!) = (47466735597972069435 / 1048576 : ℚ) := by
  rw [yRow_eq_fast]
  decide +kernel

theorem yRow_7_5_5_0 : yRow 7 5 5 (rows[0]!) = (1647590914974091305 / 512 : ℚ) := by
  rw [yRow_eq_fast]
  decide +kernel

theorem yRow_7_5_5_1 : yRow 7 5 5 (rows[1]!) = (-1941155336440971141 / 4194304 : ℚ) := by
  rw [yRow_eq_fast]
  decide +kernel

theorem yRow_7_5_5_2 : yRow 7 5 5 (rows[2]!) = (13696035226878429190755 / 16777216 : ℚ) := by
  rw [yRow_eq_fast]
  decide +kernel

theorem yRow_7_5_5_3 : yRow 7 5 5 (rows[3]!) = (21555340744289352133005 / 29360128 : ℚ) := by
  rw [yRow_eq_fast]
  decide +kernel

theorem yRow_7_5_5_4 : yRow 7 5 5 (rows[4]!) = (23982864216689624871615 / 469762048 : ℚ) := by
  rw [yRow_eq_fast]
  decide +kernel

theorem yRow_7_5_5_5 : yRow 7 5 5 (rows[5]!) = (298255256745963536707095 / 1879048192 : ℚ) := by
  rw [yRow_eq_fast]
  decide +kernel

theorem yRow_7_5_5_6 : yRow 7 5 5 (rows[6]!) = (-489275399025456543315 / 33554432 : ℚ) := by
  rw [yRow_eq_fast]
  decide +kernel

theorem yRow_7_5_7_0 : yRow 7 5 7 (rows[0]!) = (1153158553770801165 / 128 : ℚ) := by
  rw [yRow_eq_fast]
  decide +kernel

theorem yRow_7_5_7_1 : yRow 7 5 7 (rows[1]!) = (398875219468930779 / 2097152 : ℚ) := by
  rw [yRow_eq_fast]
  decide +kernel

theorem yRow_7_5_7_2 : yRow 7 5 7 (rows[2]!) = (-3344728266700356251085 / 8388608 : ℚ) := by
  rw [yRow_eq_fast]
  decide +kernel

theorem yRow_7_5_7_3 : yRow 7 5 7 (rows[3]!) = (2694741498446716664085 / 2097152 : ℚ) := by
  rw [yRow_eq_fast]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_Row073
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem yRow_7_5_7_4 : yRow 7 5 7 (rows[4]!) = (-3701247860527868239965 / 33554432 : ℚ) := by
  rw [yRow_eq_fast]
  decide +kernel

theorem yRow_7_5_7_5 : yRow 7 5 7 (rows[5]!) = (-111316765905740996833665 / 134217728 : ℚ) := by
  rw [yRow_eq_fast]
  decide +kernel

theorem yRow_7_5_7_6 : yRow 7 5 7 (rows[6]!) = (21601964370283224165 / 4194304 : ℚ) := by
  rw [yRow_eq_fast]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_Error07
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
open scoped Matrix
theorem error_7_1_1 : Y 7 1 1 = (-2223010934642432694336471/93952409600000000000000 : ℚ) := by
  rw [Y_expand, yRow_7_1_1_0, yRow_7_1_1_1, yRow_7_1_1_2, yRow_7_1_1_3, yRow_7_1_1_4, yRow_7_1_1_5, yRow_7_1_1_6]
  norm_num

theorem error_7_1_3 : Y 7 1 3 = (108477953957456824077753/23488102400000000000000 : ℚ) := by
  rw [Y_expand, yRow_7_1_3_0, yRow_7_1_3_1, yRow_7_1_3_2, yRow_7_1_3_3, yRow_7_1_3_4, yRow_7_1_3_5, yRow_7_1_3_6]
  norm_num

theorem error_7_1_5 : Y 7 1 5 = (-5196975194710104279852387/187904819200000000000000 : ℚ) := by
  rw [Y_expand, yRow_7_1_5_0, yRow_7_1_5_1, yRow_7_1_5_2, yRow_7_1_5_3, yRow_7_1_5_4, yRow_7_1_5_5, yRow_7_1_5_6]
  norm_num

theorem error_7_1_7 : Y 7 1 7 = (-1651569710015033615111331/13421772800000000000000 : ℚ) := by
  rw [Y_expand, yRow_7_1_7_0, yRow_7_1_7_1, yRow_7_1_7_2, yRow_7_1_7_3, yRow_7_1_7_4, yRow_7_1_7_5, yRow_7_1_7_6]
  norm_num

theorem error_7_3_3 : Y 7 3 3 = (-367191109045089385072113/46976204800000000000000 : ℚ) := by
  rw [Y_expand, yRow_7_3_3_0, yRow_7_3_3_1, yRow_7_3_3_2, yRow_7_3_3_3, yRow_7_3_3_4, yRow_7_3_3_5, yRow_7_3_3_6]
  norm_num

theorem error_7_3_5 : Y 7 3 5 = (117278459962852511483289/18790481920000000000000 : ℚ) := by
  rw [Y_expand, yRow_7_3_5_0, yRow_7_3_5_1, yRow_7_3_5_2, yRow_7_3_5_3, yRow_7_3_5_4, yRow_7_3_5_5, yRow_7_3_5_6]
  norm_num

theorem error_7_3_7 : Y 7 3 7 = (24425660136497504106789/1342177280000000000000 : ℚ) := by
  rw [Y_expand, yRow_7_3_7_0, yRow_7_3_7_1, yRow_7_3_7_2, yRow_7_3_7_3, yRow_7_3_7_4, yRow_7_3_7_5, yRow_7_3_7_6]
  norm_num

theorem error_7_5_5 : Y 7 5 5 = (-9326100426131028195384507/187904819200000000000000 : ℚ) := by
  rw [Y_expand, yRow_7_5_5_0, yRow_7_5_5_1, yRow_7_5_5_2, yRow_7_5_5_3, yRow_7_5_5_4, yRow_7_5_5_5, yRow_7_5_5_6]
  norm_num

theorem error_7_5_7 : Y 7 5 7 = (-1202717220838198373824731/13421772800000000000000 : ℚ) := by
  rw [Y_expand, yRow_7_5_7_0, yRow_7_5_7_1, yRow_7_5_7_2, yRow_7_5_7_3, yRow_7_5_7_4, yRow_7_5_7_5, yRow_7_5_7_6]
  norm_num

theorem error_7_s50_oai : errorRational 7 =
    !![-2223010934642432694336471/93952409600000000000000, 108477953957456824077753/23488102400000000000000, -5196975194710104279852387/187904819200000000000000, -1651569710015033615111331/13421772800000000000000;
      108477953957456824077753/23488102400000000000000, -367191109045089385072113/46976204800000000000000, 117278459962852511483289/18790481920000000000000, 24425660136497504106789/1342177280000000000000;
      -5196975194710104279852387/187904819200000000000000, 117278459962852511483289/18790481920000000000000, -9326100426131028195384507/187904819200000000000000, -1202717220838198373824731/13421772800000000000000;
      -1651569710015033615111331/13421772800000000000000, 24425660136497504106789/1342177280000000000000, -1202717220838198373824731/13421772800000000000000, -3962174270025189289538421/6710886400000000000000] := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact error_7_1_1
  · exact error_7_1_3
  · exact error_7_1_5
  · exact error_7_1_7
  · exact error_7_3_1_s50
  · exact error_7_3_3
  · exact error_7_3_5
  · exact error_7_3_7
  · exact error_7_5_1_s50
  · exact error_7_5_3_s50
  · exact error_7_5_5
  · exact error_7_5_7
  · exact error_7_7_1_s50
  · exact error_7_7_3_s50
  · exact error_7_7_5_s50
  · exact error_7_7_7_s50

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.error_7_s50_oai := @OAI.Laughlin.Certificate.error_7_s50_oai
